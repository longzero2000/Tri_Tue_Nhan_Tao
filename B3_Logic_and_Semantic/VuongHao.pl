% Thuat toan Vuong Hao.
% Xac dinh toan tu.
:-op(700,xfy,<->).
:-op(700,xfy,->).
:-op(600,xfy,v).
:-op(600,xfy,&).
:-op(500,fy,!).

% Lenh goi chinh cho chuong trinh.
prove([],[]).
prove([L|P],[R|A]):-
    nl, ansi_format([bold],'Menh de: ',[]), write(L), write(' |= '), write(R), nl, nl,
    ansi_format([bold],'Chung minh:',[]), nl, nl,
    wang(L,R),
    prove(P,A).

% Thu tuc thuat toan de chung minh menh de.
wang(L,R):-
    rules(L,R,[],0), nl,
    ansi_format([bold,fg(green)], 'Ket qua: Menh de duoc chung minh.',[]), nl, nl;
    ansi_format([bold, fg(red)],'Khong chung minh duooc o buoc hien tai!',[]), nl, nl,
    ansi_format([bold,fg(red)], 'Ket qua: Menh de sai!',[]), nl, nl.

% Di chuyen phu dinh tu trai sang phai.
rules(L,R,S,T):-
    member(!X,L),
    delete(L,!X,Ld),
    append(S,[[['*Rule 1L                 '],[Ld,' |= ',[X|R]],T]],Sa),
    rules(Ld,[X|R],Sa,T).

% Di chuyen phu dinh tu phai qua trai.
rules(L,R,S,T):-
    member(!X,R),
    delete(R,!X,Rd),
    append(S,[[['*Rule 1R                 '],[[X|L],' |= ',Rd],T]],Sa),
    rules([X|L],Rd,Sa,T).

% Thay the phep hoi bang du phay o ben trai.
rules(L,R,S,T):-
    member(X & Y,L),
    delete(L,X & Y,Ld),
    append(S,[[['*Rule 2                  '],[[X,Y|Ld],' |= ',R],T]],Sa),
    rules([X,Y|Ld],R,Sa,T).

% Thay the phep tuyen bang dau phay o ben phai.
rules(L,R,S,T):-
    member(X v Y,R),
    delete(R,X v Y,Rd),
    append(S,[[['*Rule 3                  '],[L,' |= ',[X,Y|Rd]],T]],Sa),
    rules(L,[X,Y|Rd],Sa,T).

% Tach phep tuyen ben trai.
rules(L,R,S,T):-
    member(X v Y,L),
    delete(L,X v Y,Ld),
    Ta is T + 1,
    append(S,[[['*Rule 4a - Branch Level ',T],[[X|Ld],' |= ',R],T]],Sa),
    rules([X|Ld],R,Sa,Ta),
    Tb is T + 1,
    append([],[[['*Rule 4b - Branch Level ',T],[[Y|Ld],' |= ',R],T]],Sb),
    rules([Y|Ld],R,Sb,Tb).

% Tach phep hoi ben phai.
rules(L,R,S,T):-
    member(X & Y,R),
    delete(R,X & Y, Rd),
    append(S,[[['*Rule 5a - Branch Level ',T],[L,' |= ',[X|Rd]],T]],Sa),
    Ta is T + 1,
    rules(L,[X|Rd],Sa,Ta),
    Tb is T + 1,
    append([],[[['*Rule 5b - Branch Level ',T],[L,' |= ',[Y|Rd]],T]],Sb),
    rules(L,[Y|Rd],Sb,Tb).

% Thay the phep keo theo ben trai.
rules(L,R,S,T):-
    member(X -> Y,L),
    delete(L,X -> Y,Ld),
    append(S,[[['*Rule 6L                 '],[[!X v Y|Ld],' |= ',R],T]],Sa),
    rules([!X v Y|Ld],R,Sa,T).

% Thay the phep keo theo ben phai.
rules(L,R,S,T):-
    member(X -> Y,R),
    delete(R,X -> Y,Rd),
  append(S,[[['*Rule 6R                 '],[L,' |= ',[!X v Y|Rd]],T]],Sa),
    rules(L,[!X v Y|Rd],Sa,T).

% Thay the phep tuong duong ben trai.
rules(L,R,S,T):-
    member(X <-> Y,L),
    delete(L,X <-> Y,Ld),
    append(S,[[['*Rule 7L                 '],[[(X -> Y) & (Y -> X)|Ld],' |= ',R],T]],Sa),
    rules([(X -> Y) & (Y -> X)|Ld],R,Sa,T).

% Thay the phep tuong duong ben phai.
rules(L,R,S,T):-
    member(X <-> Y,R),
    delete(R,X <-> Y,Rd),
    append(S,[[['*Rule 7R                 '],[L,' |= ',[(X -> Y) & (Y -> X)|Rd]],T]],Sa),
    rules(L,[(X -> Y) & (Y -> X)|Rd],Sa,T).

% So sánh hai ve menh de.
rules(L,R,S,T):-
    append(S,[[['*Tautology?              '],[L,' |= ',R], T]],Sa),
    member(X,L),
    member(X,R),
    append(Sa,[[['*True.                   '],[],T]],Sb),
    printprove(Sb).

% Neu menh de dung thi in ra dieu phai chung minh.
printprove([]).
printprove([[P,Q,T]|S]):-
  tab(T*5), printlist(P), tab(40 - T*5), printlist(Q), nl,
    printprove(S).

% In danh sach theo de quy.
printlist([]).
printlist([H|T]):-
    write(H),
    printlist(T).
