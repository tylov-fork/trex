/***************************************************************
	T-Rex a tiny regular expression library

	Copyright (C) 2003-2004 Alberto Demichelis

	see copyright notice in TRex.h
****************************************************************/
#include <malloc.h>
#include <string.h>
#include <ctype.h>
#include <setjmp.h>
#include "TRex.h"

#ifdef _DEBUG
#include <stdio.h>

static const TRexChar *g_nnames[] =
{
	_TREXC("NONE"),_TREXC("OP_GREEDY"),	_TREXC("OP_OR"),
	_TREXC("OP_EXPR"),_TREXC("OP_DOT"),	_TREXC("OP_CLASS"),
	_TREXC("OP_NCLASS"),_TREXC("OP_RANGE"),_TREXC("OP_CHAR"),
	_TREXC("OP_EOL"),_TREXC("OP_BOL")
};

#endif

#define OP_GREEDY		MAX_CHAR+1 // * + ? {n}
#define OP_OR			MAX_CHAR+2
#define OP_EXPR			MAX_CHAR+3 //parentesis ()
#define OP_DOT			MAX_CHAR+4
#define OP_CLASS		MAX_CHAR+5
#define OP_NCLASS		MAX_CHAR+6 //negates class the [^
#define OP_RANGE		MAX_CHAR+7
#define OP_CHAR			MAX_CHAR+8
#define OP_EOL			MAX_CHAR+9
#define OP_BOL			MAX_CHAR+10

#define TREX_SYMBOL_ANY_CHAR '.'
#define TREX_SYMBOL_GREEDY_ONE_OR_MORE '+'
#define TREX_SYMBOL_GREEDY_ZERO_OR_MORE '*'
#define TREX_SYMBOL_GREEDY_ZERO_OR_ONE '?'
#define TREX_SYMBOL_BRANCH '|'
#define TREX_SYMBOL_END_OF_STRING '$'
#define TREX_SYMBOL_BEGINNING_OF_STRING '^'
#define TREX_SYMBOL_ESCAPE_CHAR '\\'


typedef int TRexNodeType;

typedef struct tagTRexNode{
	TRexNodeType type;
	long left;
	long right;
	int next;
}TRexNode;

struct TRex{
	const TRexChar *_eol;
	const TRexChar *_bol;
	const TRexChar *_p;
	int _first;
	int _op;
	TRexNode *_nodes;
	int _nallocated;
	int _nsize;
	int _nsubexpr;
	TRexMatch *_matches;
	int _currsubexp;
	void *_jmpbuf;
	const TRexChar **_error;
};

static int trex_list(TRex *exp);

static int trex_newnode(TRex *exp, TRexNodeType type)
{
	TRexNode n;
	n.type = type;
	n.next = n.right = n.left = -1;
	if(type == OP_EXPR)
		n.right = exp->_nsubexpr++;
	if(exp->_nallocated < (exp->_nsize + 1)) {
		exp->_nallocated *= 2;
		exp->_nodes = (TRexNode *)realloc(exp->_nodes,exp->_nallocated * sizeof(TRexNode));
	}
	exp->_nodes[exp->_nsize++] = n;
	return (int)exp->_nsize - 1;
}

static void trex_error(TRex *exp,const TRexChar *error)
{
	if(exp->_error) *exp->_error = error;
	longjmp(*((jmp_buf*)exp->_jmpbuf),-1);
}

static void trex_expect(TRex *exp, int n){
	if((*exp->_p) != n) 
		trex_error(exp, _TREXC("expected paren"));
	*exp->_p++;
}

static TRexBool trex_ischar(TRexChar c)
{
	switch(c) {
	case TREX_SYMBOL_BRANCH:case TREX_SYMBOL_GREEDY_ZERO_OR_MORE:
	case TREX_SYMBOL_GREEDY_ZERO_OR_ONE:case TREX_SYMBOL_GREEDY_ONE_OR_MORE:
	case TREX_SYMBOL_BEGINNING_OF_STRING:case TREX_SYMBOL_END_OF_STRING:
	case TREX_SYMBOL_ANY_CHAR:case TREX_SYMBOL_ESCAPE_CHAR:case '(':case ')':case '[':case '{': case '}':
		return TRex_False;
    }
	return TRex_True;
}

static TRexChar trex_escapechar(TRex *exp)
{
	switch(*exp->_p) {
	case 'n': *exp->_p++; return '\n';
	case 't': *exp->_p++; return '\t';
	case 'r': *exp->_p++; return '\r';
	case 'f': *exp->_p++; return '\f';
	default: return (*exp->_p++);
	}
}

static TRexChar trex_char(TRex *exp)
{
	if(*exp->_p == TREX_SYMBOL_ESCAPE_CHAR){ *exp->_p++; return trex_escapechar(exp); }
	else if(!trex_ischar(*exp->_p)) trex_error(exp,_TREXC("letter expected"));
	return (*exp->_p++);
}

static int trex_class(TRex *exp)
{
	int ret = -1;
	int first = -1,chain;
	if(*exp->_p == TREX_SYMBOL_BEGINNING_OF_STRING){
		ret = trex_newnode(exp,OP_NCLASS);
		*exp->_p++;
	}else ret = trex_newnode(exp,OP_CLASS);
	
	if(*exp->_p == ']' || *exp->_p == '-'){
		first = *exp->_p;
		*exp->_p++;
	}
	chain = ret;
	while(*exp->_p != ']' && exp->_p != exp->_eol) {
		if(*exp->_p == '-' && first != -1){ 
			int r;
			if(*exp->_p++ == ']') trex_error(exp,_TREXC("unfinished range"));
			r = trex_newnode(exp,OP_RANGE);
			if(first>*exp->_p) trex_error(exp,_TREXC("invalid range"));
			exp->_nodes[r].left = first;
			exp->_nodes[r].right = trex_char(exp);
            exp->_nodes[chain].next = r;
			chain = r;
			first = -1;
		}
		else{
			if(first!=-1){
				int c = trex_newnode(exp,first);
				exp->_nodes[chain].next = c;
				chain = c;
				first = trex_char(exp);
			}
			else{
				first = trex_char(exp);
			}
		}
	}
	if(first!=-1){
		int c = trex_newnode(exp,first);
		exp->_nodes[chain].next = c;
		chain = c;
		first = -1;
	}
	/* hack? */
	exp->_nodes[ret].left = exp->_nodes[ret].next;
	exp->_nodes[ret].next = -1;
	return ret;
}

static int trex_parsenumber(TRex *exp)
{
	int ret = *exp->_p-'0';
	int positions = 10;
	*exp->_p++;
	while(isdigit(*exp->_p)) {
		ret = ret*10+(*exp->_p++-'0');
		if(positions==1000000000) trex_error(exp,_TREXC("overflow in numeric constant"));
		positions *= 10;
	};
	return ret;
}

static int trex_element(TRex *exp)
{
	int ret;
	switch(*exp->_p)
	{
	case '(': {
		int expr;
		*exp->_p++;
		expr = trex_newnode(exp,OP_EXPR);
		exp->_nodes[expr].left = trex_list(exp);
		ret = expr;
		trex_expect(exp,')');
	}
		break;
	case '[':
		*exp->_p++;
		ret = trex_class(exp);
		trex_expect(exp,']');
		break;
	case TREX_SYMBOL_END_OF_STRING: *exp->_p++; ret = trex_newnode(exp,OP_EOL);break;
	case TREX_SYMBOL_ANY_CHAR: *exp->_p++; ret = trex_newnode(exp,OP_DOT);break;
	default:
		ret = trex_newnode(exp,trex_char(exp));
		break;
	}
	/* scope block */
	{
		int op;
		unsigned short p0 = 0, p1 = 0;
		switch(*exp->_p){
		case TREX_SYMBOL_GREEDY_ZERO_OR_MORE: p0 = 0; p1 = 0xFFFF; *exp->_p++; goto __end;
		case TREX_SYMBOL_GREEDY_ONE_OR_MORE: p0 = 1; p1 = 0xFFFF; *exp->_p++; goto __end;
		case TREX_SYMBOL_GREEDY_ZERO_OR_ONE: p0 = 0; p1 = 1; *exp->_p++; goto __end;
		case '{':{
			*exp->_p++;
			if(!isdigit(*exp->_p)) trex_error(exp,_TREXC("number expected"));
			p0 = trex_parsenumber(exp);
			switch(*exp->_p) {
			case '}':
				p1 = p0; *exp->_p++;
				goto __end;
			case ',':
				*exp->_p++;
				p1 = 0xFFFF;
				if(isdigit(*exp->_p)){
					p1 = trex_parsenumber(exp);
				}
				trex_expect(exp,'}');
				goto __end;
			default:
				trex_error(exp,_TREXC(", or } expected"));
			}
		}
		__end: {
				int nnode = trex_newnode(exp,OP_GREEDY);
				op = OP_GREEDY;
				exp->_nodes[nnode].left = ret;
				exp->_nodes[nnode].right = ((p0)<<16)|p1;
				ret = nnode;
			}
		}
	}
	if(*exp->_p != TREX_SYMBOL_BRANCH && *exp->_p != ')' && *exp->_p != TREX_SYMBOL_GREEDY_ZERO_OR_MORE && *exp->_p != TREX_SYMBOL_GREEDY_ONE_OR_MORE && *exp->_p != '\0')
		exp->_nodes[ret].next = trex_element(exp);
	return ret;
}

static int trex_list(TRex *exp)
{
	int ret=-1,e;
	if(*exp->_p == TREX_SYMBOL_BEGINNING_OF_STRING) {
		*exp->_p++;
		ret = trex_newnode(exp,OP_BOL);
	}
	e = trex_element(exp);
	if(ret != -1) {
		exp->_nodes[ret].next = e;
	}
	else ret = e;

	if(*exp->_p == TREX_SYMBOL_BRANCH) {
		int temp;
		*exp->_p++;
		temp = trex_newnode(exp,OP_OR);
		exp->_nodes[temp].left = ret;
		exp->_nodes[temp].right = trex_list(exp);
		ret = temp;
	}
	return ret;
}

static TRexBool trex_matchclass(TRex* exp,TRexNode *node,TRexChar c)
{
	do {
		if(node->type == OP_RANGE) {
			if(c >= node->left && c <= node->right)return TRex_True;
		}
		else {
			if(c == node->type)return TRex_True;
		}
	} while((node->next != -1) && (node = &exp->_nodes[node->next]));
	return TRex_False;
}

static const TRexChar *trex_matchnode(TRex* exp,TRexNode *node,const TRexChar *str)
{
	TRexNodeType type = node->type;
	switch(type) {
	case OP_GREEDY: {
		int p0 = (node->right >> 16)&0x0000FFFF, p1 = node->right&0x0000FFFF, nmaches = 0;
		const TRexChar *s=str, *good = str;
		while((nmaches == 0xFFFF || nmaches < p1) && (s = trex_matchnode(exp,&exp->_nodes[node->left],s))) {
			good=s;
			nmaches++;
		}
		if(p0 == p1 && p0 == nmaches) return good;
		else if(nmaches >= p0 && p1 == 0xFFFF) return good;
		else if(nmaches >= p0 && nmaches <= p1) return good;
		return NULL;
	}
	case OP_OR: {
			const TRexChar *asd = str;
			TRexNode *temp=&exp->_nodes[node->left];
			while(asd = trex_matchnode(exp,temp,asd)) {
				if(temp->next != -1)
					temp = &exp->_nodes[temp->next];
				else
					return asd;
			}
			asd = str;
			temp = &exp->_nodes[node->right];
			while(asd = trex_matchnode(exp,temp,asd)) {
				if(temp->next != -1)
					temp = &exp->_nodes[temp->next];
				else
					return asd;
			}
			return NULL;
			break;
	}
	case OP_EXPR: {
			TRexNode *n = &exp->_nodes[node->left];
			const TRexChar *cur = str;
			int capture = -1;
			if(node->right == exp->_currsubexp) {
				capture = exp->_currsubexp;
				exp->_matches[capture].begin = cur;
				exp->_currsubexp++;
			}

			do {
				if(!(cur = trex_matchnode(exp,n,cur))) {
					if(capture != -1){
						exp->_matches[capture].begin = 0;
						exp->_matches[capture].len = 0;
					}
					return NULL;
				}
			} while((n->next != -1) && (n = &exp->_nodes[n->next]));

			if(capture != -1) 
				exp->_matches[capture].len = cur - exp->_matches[capture].begin;
			return cur;
	}				 
	case OP_BOL:
		if(str == exp->_bol) return str;
		return NULL;
	case OP_EOL:
		if(str == exp->_eol) return str;
		return NULL;
	case OP_DOT:
		*str++;
		return str;
	case OP_NCLASS:
	case OP_CLASS:
		if(trex_matchclass(exp,&exp->_nodes[node->left],*str)?(type == OP_CLASS?TRex_True:TRex_False):(type == OP_NCLASS?TRex_True:TRex_False)) {
			*str++;
			return str;
		}
		return NULL;
	default: /* char */
		if(*str != node->type) return NULL;
		*str++;
		return str;
	}
	return NULL;
}

/* public api */
TRex *trex_compile(const TRexChar *pattern,const TRexChar **error)
{
	TRex *exp = malloc(sizeof(TRex));
	exp->_p = pattern;
	exp->_nallocated = (int)trex_strlen(pattern) * sizeof(TRexChar);
	exp->_nodes = (TRexNode *)malloc(exp->_nallocated * sizeof(TRexNode));
	exp->_nsize = 0;
	exp->_matches = 0;
	exp->_nsubexpr = 0;
	exp->_first = trex_newnode(exp,OP_EXPR);
	exp->_error = error;
	exp->_jmpbuf = malloc(sizeof(jmp_buf));
	if(setjmp(*((jmp_buf*)exp->_jmpbuf)) == 0) {
		exp->_nodes[exp->_first].left=trex_list(exp);
		if(*exp->_p!='\0')
			trex_error(exp,_TREXC("unexpected character"));
#ifdef _DEBUG
		{
			int nsize,i;
			TRexNode *t;
			nsize = exp->_nsize;
			t = &exp->_nodes[0];
			trex_printf(_TREXC("\n"));
			for(i = 0;i < nsize; i++) {
				if(exp->_nodes[i].type>MAX_CHAR)
					trex_printf(_TREXC("[%02d] %10s "),i,g_nnames[exp->_nodes[i].type-MAX_CHAR]);
				else
					trex_printf(_TREXC("[%02d] %10c "),i,exp->_nodes[i].type);
				trex_printf(_TREXC("left %02d right %02d next %02d\n"),exp->_nodes[i].left,exp->_nodes[i].right,exp->_nodes[i].next);
			}
			trex_printf(_TREXC("\n"));
		}
#endif
		exp->_matches = (TRexMatch *) malloc(exp->_nsubexpr * sizeof(TRexMatch));
		memset(exp->_matches,0,exp->_nsubexpr * sizeof(TRexMatch));
	}
	else{
		trex_free(exp);
		return NULL;
	}
	return exp;
}

void trex_free(TRex *exp)
{
	if(exp)	{
		if(exp->_nodes) free(exp->_nodes);
		if(exp->_jmpbuf) free(exp->_jmpbuf);
		if(exp->_matches) free(exp->_matches);
		free(exp);
	}
}

TRexBool trex_match(TRex* exp,const TRexChar* text)
{
	const TRexChar* res = NULL;
	exp->_bol = text;
	exp->_eol = text + trex_strlen(text);
	exp->_currsubexp = 0;
	res = trex_matchnode(exp,exp->_nodes,text);
	if(res == NULL || res != exp->_eol)
		return TRex_False;
	return TRex_True;
}

TRexBool trex_searchrange(TRex* exp,const TRexChar* text_begin,const TRexChar* text_end,const TRexChar** out_begin, const TRexChar** out_end)
{
	const TRexChar *cur = NULL;
	int node = exp->_first;
	exp->_bol = text_begin;
	exp->_eol = text_end;
	do {
		cur = text_begin;
		while(node != -1) {
			exp->_currsubexp = 0;
			cur = trex_matchnode(exp,&exp->_nodes[node],cur);
			if(!cur)
				break;
			node = exp->_nodes[node].next;
		}
		*text_begin++;
	} while(cur == NULL && text_begin != text_end);

	if(cur == NULL)
		return TRex_False;

	--text_begin;

	if(out_begin) *out_begin = text_begin;
	if(out_end) *out_end = cur;
	return TRex_True;
}

TRexBool trex_search(TRex* exp,const TRexChar* text, const TRexChar** out_begin, const TRexChar** out_end)
{
	return trex_searchrange(exp,text,text + trex_strlen(text),out_begin,out_end);
}

int trex_getsubexpcount(TRex* exp)
{
	return exp->_nsubexpr;
}

TRexBool trex_getsubexp(TRex* exp, int n, TRexMatch *subexp)
{
	if( n<0 || n >= exp->_nsubexpr) return TRex_False;
	*subexp = exp->_matches[n];
	return TRex_True;
}

