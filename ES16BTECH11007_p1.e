note
	author : "Saurav vara prasad Channuri"
	RollNo: "ES16BTECH11007"
	program: "Question 1 : INVERSE OF A MATRIX"
	course : "Principles of Programming Language"

class
	ES16BTECH11007_P1
create 
	make
feature
	divi(Aa: ARRAY2[REAL]; nn : INTEGER) : BOOLEAN
		require 
			checkin : nn > 0		
		local 
			dd : REAL
		do
				from
					i := 1
				invariant
					TRUE
				until
					i > n
				loop
					dd := Aa.item(i,i)
					--print(dd)					
					if dd = 0
					then
					--	print("yes")
						Result := True
					end
						from	
							j := 1
						invariant
							TRUE
						until
							j > 2*nn
						loop
							Aa.item(i,j) := Aa.item(i,j)/dd
							j := j + 1
						end
					i := i + 1
				end
		ensure
			Result = True or Result = False

		end


	make
		do

			invalid := False
			Io.read_integer
			n := Io.last_integer						
			!!A.make(2*n,2*n)
			create P.make(1)

		 if n < 0
		 then
			Io.set_error_default
			Io.put_string("%NINVALID%N")
			Io.set_output_default
		 else  
				
-------------------------------------------------------------------
--                    INPUT LOOP
			

			from
				j := 1
			invariant
				TRUE
			until   
				j > N
			loop  
				from
					i := 1
				invariant
					TRUE
				until
					i > N 
				loop
					Io.read_real
					A.put(Io.last_real, j, i)	
					i := i + 1
				end
				j := j + 1
			end

--------------------------------------------------------------------
			--print("%N1 - done%N")

			from
				i:= 1
			invariant
				TRUE
			until
				i > n
			loop
					from
						j:=1
					invariant
						TRUE
					until
						j > 2*n
					loop
							if j = i + n
							then							
								A.item(i,j) := 1		
							end

						j := j + 1			
					end
				i := i + 1
			end

---------------------------------------------------------------------
			--print("%N2 - done%N")
			from
				i := n
			invariant
				TRUE
			until
				i < 2
			loop

				if A.item(i-1,1) < A.item(i,1)
				then
					from
						j:=1
					invariant
						TRUE
					until
						j > 2*n
					loop
						d := A.item(i,j)
						A.item(i,j) := A.item(i-1, j)
						A.item(i-1,j) := d
						j := j + 1						
			
					end
				end

				i := i - 1
			end

-----------------------------------------------------------------------
--                      AUGMENTED
-----------------------------------------------------------------------
		--	print("%N3 - done%N")
		--	print("augmented%N")
			from
				i:= 1
			invariant
				TRUE
			until
				i > n
			loop
					from
						j:=1
					invariant
						TRUE
					until
						j > 2*n
					loop
		--				print(A.item(i,j).out + " ")
						j := j + 1			
					end
		--		print("%N")
				i := i + 1
			end

------------------------------------------------------------------------
		--	print("%N4 - done%N")
			from
				i := 1
			invariant
				TRUE
			until
				i > n
			loop

					from
						j := 1
					invariant
						TRUE
					until
						j > 2*n
					loop	


							if j>i or i>j
							then
								d := A.item(j,i)/A.item(i,i)
								--print(A.item(i,i))
								if A.item(i,i) = 0
								then
									invalid := True
									count := 1
								end

								from
									k := 1
								invariant
									TRUE
								until
									k > 2*n
								loop
									A.item(j,k) := A.item(j,k) - (A.item(i,k)*d)                              
									k:= k + 1
								end
							end
						j := j + 1
					end
				i := i + 1
			end

			
-------------------------------------------------------------------------
		--	print("%N5 - done%N")
			invalid := divi(A,n)
			--count := 0
--------------------------------------------------------------------------

--------------------------------------------------------------------------
--                   INVERSE MATRIX
		--	print("%N6 - done%N")
		--	print("%Ninverse matrix%N")
			if invalid = True or count = 1
			then
				Io.set_error_default
				Io.put_string("%NINVALID%N")
				Io.set_output_default			
				
			else


				from
					i:= 1
				invariant
					TRUE
				until
					i > n
				loop
						from
							j := n+1
						invariant
							TRUE
						until
							j > 2*n
						loop
							print(A.item(i,j).out + " " )
							j:= j + 1			
						end
					print("%N")
					i := i + 1
				end
			end				

	        end
		

	end
A : ARRAY2[REAL]
d : REAL
i,j,k,n : INTEGER
count, count1, size : INTEGER
Kk : CHARACTER
invalid, validBase : BOOLEAN
p : STRING

end

