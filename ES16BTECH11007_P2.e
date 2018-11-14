note
	author : "Saurav vara prasad Channuri"
	RollNo: "ES16BTECH11007"
	program: "Question 2 : STABLE MARRIAGE PROBLEM"
	course : "Principles of Programming Language"

class 
	ES16BTECH11007_P2
create 
	make
feature


	printMatrix(A : ARRAY2[REAL] ; dimension : INTEGER)
		require
			dimension > 0
		do			
			from
				i:= 1
			invariant
				TRUE
			until
				i > dimension
			loop
				from
					j:=1
				invariant
					TRUE
				until
					j > dimension + 1
				loop
					print(A.item(i,j).out + " ")
					j := j + 1
				end
				i := i + 1
				print("%N")
			end			
			print("%N")
		ensure
			A = old A
		end



-------------------------------------------------------------------------------------

	checkZeros(A: ARRAY[REAL] ; sizet : INTEGER): BOOLEAN
		require
			CorDimension : sizet > 0

		do
			Result := False

			from
				i := 1
			invariant
				TRUE
			until
				i > sizet
			loop
				if A.item(i) = 0
				then
					Result := True
				end
				i := i + 1
			end
		ensure
			A = old A
		end
-------------------------------------------------------------------------------------
-- 



-------------------------------------------------------------------------------------	
	checkW(man1: ARRAY[REAL]; woman1: ARRAY[REAL]; men1: ARRAY2[REAL]; women1: ARRAY2[REAL];married1: ARRAY[REAL]; size1: INTEGER; tw: INTEGER; nm : INTEGER) 
		require
			tw > 0 and nm > 0 and size1> 0		
		local
			zeroYes, paired : BOOLEAN
			pairedMan, iter, preferencePairedMan, preferenceNewMan : INTEGER
		do
			preferenceNewMan := 0
			preferencePairedMan := 0
			
			from
				i := 1
			invariant
				TRUE
			until
				i > size1
			loop
				if married1.item(i) = tw
				then
					pairedMan := i
				end
				i := i + 1
			end
			
	

			from
				i := 2
			invariant
				TRUE
			until
				i > size1 + 1				
			loop
				if women1.item(tw,i) = pairedMan
				then
					preferencePairedMan := i
				end

				i := i + 1
			end

							
			from
				i := 2
			invariant
				i<size1 + 1 and i >= 2 
			until
				i > size1 + 1
			loop
				if women1.item(tw,i) = nm
				then
					preferenceNewMan := i
				end
				i := i + 1 
			end

					if (preferenceNewMan = 0 or preferencePairedMan = 0) or (preferenceNewMan = preferencePairedMan)
					then
						Io.set_error_default
						Io.put_string("%NINVALID%N")
						Io.set_output_default
					end

			if preferenceNewMan < preferencePairedMan -- new man more preferred 
			then
				married1.item(pairedMan) := 0     -- paired man freed
				married1.item(nm) := tw           -- new man paired			
				man1.item(pairedMan) := 0
				man1.item(nm) := 1			
			end
		ensure
			 (men1 = old men1) and (women1 = old women1)
		end


----------------------------------------------------------------------------------------------------------------------------

	checkS( man1:ARRAY[REAL] ; woman1:ARRAY[REAL] ; men1:ARRAY2[REAL] ; women1:ARRAY2[REAL] ; married1:ARRAY[REAL] ; size1:INTEGER ; t:INTEGER ) 
		require		
			checking : size1 > 0 and t > 0
		local
			zeroYes : BOOLEAN
			paired : BOOLEAN
			pairedMan : INTEGER
			iter : INTEGER		
		do
			iter := 2
			paired := False
			
			from
				 paired := False
			invariant
				 TRUE				
			until
				 paired = True or iter > size1
			loop
				if woman1.item(men1.item(t,iter).rounded) = 0  -- woman of his highest preference hasn't been proposed yet / unpaired
				then
					married1.item(t) := men1.item(t,iter)
					woman1.item(men1.item(t,iter).rounded) := 1
					man1.item(t) := 1
					paired := True
				else                                -- woman is paired
					checkW(man1, woman1, men1, women1, married1, size1, men1.item(t,iter).rounded, t) 
					--paired := True
				end
				iter := iter + 1
			end
		ensure
			checking1 :man1.item(t) = 0 or man1.item(t) = 1 
		end
-------------------------------------------------------------------------------------

	make
		do
			valid := True
			--print("enter number marriages%N")		
			Io.read_integer
			N := Io.last_integer
			!!men.make(N,N+1)
			!!women.make(N,N+1)

			create man.make(1,N)
			create woman.make(1,N)
			create married.make(1,N)
			create P.make(1)

-------------------------------------------------------------------------------------
--                 WOMEN PREFERENCE INPUTS

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
					i > N + 1
				loop 
					Io.read_real
					women.put(Io.last_real, j, i)	
					i := i + 1
				end
				j := j + 1
			end

			
------------------------------------------------------------------------------------
--                 MAN PREFERENCE INPUTS



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
					i > N + 1
				loop
					Io.read_real
					men.put(Io.last_real, j, i)	
					i := i + 1
				end
				j := j + 1
			end
			--print("done")

--------------------------------------------------------------------------------------

			from
				i := 1
			invariant
				TRUE
			until
				i > N
			loop
				from 
					j := 2
				invariant
					TRUE
				until
					j > N + 1
				loop
					from
						iT := 2
					invariant
						TRUE
					until
						iT > N + 1
					loop
						if (men.item(i,j) = men.item(i,iT) and j/=iT)
						then
							valid := False
						end
						
						if men.item(i,iT).rounded > N
						then
							valid := False
						end

						iT := iT + 1
					end
					j := j + 1
				end
				i := i + 1
			end 

			--print("done 2")

			
			from
				i := 1
			invariant
				TRUE
			until
				i > N
			loop
				from 
					j := 2
				invariant
					TRUE
				until
					j > N + 1
				loop
					from
						iT := 2
					invariant
						TRUE
					until
						iT > N + 1
					loop
						if (women.item(i,j) = women.item(i,iT) and j/=iT) 
						then
							valid := False
						end
				
						if women.item(i,iT).rounded > N
						then
							valid := False
						end

						iT := iT + 1
					end
					j := j + 1
				end
				i := i + 1
			end 

---------------------------------------------------------------------
			from
				i := 1
			invariant
				TRUE
			until
				i > N
			loop
				from
					j := 1
				invariant
					TRUE
				until 
					j > N
				loop
					if men.item(i,1) = men.item(j,1) and j/=i
					then
						valid := False
					end
					j := j + 1
				end
				i := i + 1
			end	

			from
				i := 1
			invariant
				TRUE
			until
				i > N
			loop
				from
					j := 1
				invariant
					TRUE
				until 
					j > N
				loop
					if women.item(i,1) = women.item(j,1) and j/=i
					then
						valid := False
					end
					j := j + 1
				end
				i := i + 1
			end				

--------------------------------------------------------------------------------------
--                INITIALIZE MAN,WOMAN TO ZEROS

			from
				i := 1
			invariant
				TRUE
			until
				i > N
			loop
				man.item(i) := 0      -- initially all are unpaired
				woman.item(i) := 0
				i := i + 1			
			end 

---------------------------------------------------------------------------------------
--		checking for each man
			if valid = False
			then
				Io.set_error_default
				Io.put_string("%NINVALID%N")
				Io.set_output_default
			else

				unpaired := checkZeros(man,N)

	
				from
					unpaired := True
				invariant
						TRUE
				until
					unpaired = False
				loop
				
					
					from
						i := 1
					invariant
						TRUE
					until
	  					i > N 
					loop
						--print(i.out + " ")
						if man.item(i) = 0  -- man hasn't proposed anyone yet
						then
							
							checkS(man, woman,men,women,married, N, i)
						end	
						i := i + 1
					end
						--print("%N")
					unpaired := checkZeros(man,N)
				end
	
	-----------------------------------------------------------------------------------------
	--               Print final output
	
				
					from
						i := 1
					invariant
						TRUE
					until
						i > N
					loop
						print(married.item(i).out + "%N")
						i := i + 1			
					end
			end
				

		end

men, women : ARRAY2[REAL]
man, woman, married : ARRAY[REAL]
i,j,iT, N, count, count1, size, common : INTEGER
unpaired, valid : BOOLEAN
P: STRING
Kk : CHARACTER
end
