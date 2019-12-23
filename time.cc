#include <boost/multiprecision/cpp_int.hpp>
#include <iostream>
#include <chrono>

#define NOW std::chrono::high_resolution_clock::now();
#define TIME(a,b) std::chrono::duration_cast<std::chrono::microseconds>(a-b).count()

using namespace boost::multiprecision;

int main(){
	using num = cpp_int;
	num a = 1;
	for(int i=1;i<=400;++i) a*=5;
	num b = 32411343*a;
	auto t_start = NOW;
	for(int i=0;i<90;++i){
		num z = a * b;
		a+=234525675;
	}
	auto t_end = NOW;
	std::cout<<TIME(t_end,t_start)<<std::endl;

}
