#include <stdio.h>
#include <stdlib.h>

extern int our_code_starts_here() asm("our_code_starts_here");

int print(int val) {
	//if true, print "true", else if false p false, else p number? (bitwise adjustments needed)
  if(val == 0xffffffff)
  	printf("true\n");

  else if (val == 0x7fffffff)
  	printf("false\n");

  else
  {
  	val = val >> 1; 
  	printf("%d\n", val);
  }

  return val;
}

//error function?
void error(int code, int v)
{
	if(code == 0) {
		fprintf(stderr, "Error: expected a number but got %#010x\n", v);
	}
	else if (code == 1) {
		fprintf(stderr, "Error: expected a boolean but got %#010x\n", v);
	}
	else if (code == 2){
		fprintf(stderr, "Error: arithmetic overflow.");
	}
	exit(1);
}

int main(int argc, char** argv) {
  int result = our_code_starts_here();
  print(result);
  return 0;
}
