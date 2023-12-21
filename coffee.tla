------------------------------ MODULE coffee ---------------------------------------
EXTENDS Integers, TLC, Sequences

(*--algorithm CM
variables
    init = FALSE,
    menu = FALSE,
    term = FALSE,
    gl = FALSE,
    cp = FALSE,
    opc = FALSE,
    water = FALSE,
    p = FALSE,
    o = FALSE,
    w = FALSE,
    nog = FALSE,
    glassRemoved = FALSE,
    okPressed = FALSE;
    
define
\* SAFETY
    NOGLASSPAY == (term => gl)
    NOOPEN == (o => p)
    NOGLASSPREP == (opc \/ water => gl)
\*    NOTWICEPREP == ((opc \/ water) ~> O[](~(opc \/ water)))
    NOCOFFEEINWATER == [](water ~> <>(~opc))
    WILLGOTOPAY == ([](init ~> <>term))
end define;

procedure NoCoffee()
begin
   s5:
    cp := FALSE;
    goto s5;
   s6:
    p := TRUE;
    o := TRUE;
    goto s6;
   s8:
    o := FALSE;
    p := FALSE;
    goto to_ret;
   to_ret:
    return;
end procedure;

fair process Machine = "Machine" begin
    s0:
        await init = TRUE;
        init := FALSE;
        glassRemoved := FALSE;
    s1:
        while (TRUE) do
        init := FALSE;
        menu := TRUE;
           either 
                s9:
                    nog := TRUE;
                    await glassRemoved = TRUE;
                    glassRemoved := FALSE;
                    goto s1;
            or
                s2:
                    gl := TRUE;
                    term := TRUE;
                    either goto s2; \* BAD PAY
                    or
                        goto s0;
                    or 
                        s3:
                            term := FALSE;
                            cp := TRUE;
                            either call NoCoffee();
                            or
                                s8:
                                    cp := FALSE;
                                    opc := TRUE;
                                    goto s4;
                            end either;
                    or
                        s4:
                            water := TRUE;
                            opc := FALSE;
                        s7:
                            water := FALSE;
                            w := TRUE;
                            await glassRemoved = TRUE;
                            glassRemoved := FALSE;
                            gl := FALSE;
                            goto s0;
                    end either;
              end either;
        end while;
end process;

fair process User = "User" begin
    in:
      init := TRUE;
    cyc:
    while (TRUE) do
    either setGlass:
        await nog = TRUE;
        nog := FALSE;
    or
    getGlass:
        await w = TRUE;
        w := FALSE;
        glassRemoved := TRUE;
        goto in;
    end either; 
    end while;
end process;

end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "4202a052" /\ chksum(tla) = "37b5def8")
\* Label s8 of procedure NoCoffee at line 40 col 5 changed to s8_
VARIABLES init, menu, term, gl, cp, opc, water, p, o, w, nog, glassRemoved, 
          okPressed, pc, stack

(* define statement *)
NOGLASSPAY == (term => gl)
NOOPEN == (o => p)
NOGLASSPREP == (opc \/ water => gl)

NOCOFFEEINWATER == [](water ~> <>(~opc))
WILLGOTOPAY == ([](init ~> <>term))


vars == << init, menu, term, gl, cp, opc, water, p, o, w, nog, glassRemoved, 
           okPressed, pc, stack >>

ProcSet == {"Machine"} \cup {"User"}

Init == (* Global variables *)
        /\ init = FALSE
        /\ menu = FALSE
        /\ term = FALSE
        /\ gl = FALSE
        /\ cp = FALSE
        /\ opc = FALSE
        /\ water = FALSE
        /\ p = FALSE
        /\ o = FALSE
        /\ w = FALSE
        /\ nog = FALSE
        /\ glassRemoved = FALSE
        /\ okPressed = FALSE
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "Machine" -> "s0"
                                        [] self = "User" -> "in"]

s5(self) == /\ pc[self] = "s5"
            /\ cp' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << init, menu, term, gl, opc, water, p, o, w, nog, 
                            glassRemoved, okPressed, stack >>

s6(self) == /\ pc[self] = "s6"
            /\ p' = TRUE
            /\ o' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "s6"]
            /\ UNCHANGED << init, menu, term, gl, cp, opc, water, w, nog, 
                            glassRemoved, okPressed, stack >>

s8_(self) == /\ pc[self] = "s8_"
             /\ o' = FALSE
             /\ p' = FALSE
             /\ pc' = [pc EXCEPT ![self] = "to_ret"]
             /\ UNCHANGED << init, menu, term, gl, cp, opc, water, w, nog, 
                             glassRemoved, okPressed, stack >>

to_ret(self) == /\ pc[self] = "to_ret"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << init, menu, term, gl, cp, opc, water, p, o, w, 
                                nog, glassRemoved, okPressed >>

NoCoffee(self) == s5(self) \/ s6(self) \/ s8_(self) \/ to_ret(self)

s0 == /\ pc["Machine"] = "s0"
      /\ init = TRUE
      /\ init' = FALSE
      /\ glassRemoved' = FALSE
      /\ pc' = [pc EXCEPT !["Machine"] = "s1"]
      /\ UNCHANGED << menu, term, gl, cp, opc, water, p, o, w, nog, okPressed, 
                      stack >>

s1 == /\ pc["Machine"] = "s1"
      /\ init' = FALSE
      /\ menu' = TRUE
      /\ \/ /\ pc' = [pc EXCEPT !["Machine"] = "s9"]
         \/ /\ pc' = [pc EXCEPT !["Machine"] = "s2"]
      /\ UNCHANGED << term, gl, cp, opc, water, p, o, w, nog, glassRemoved, 
                      okPressed, stack >>

s9 == /\ pc["Machine"] = "s9"
      /\ nog' = TRUE
      /\ glassRemoved = TRUE
      /\ glassRemoved' = FALSE
      /\ pc' = [pc EXCEPT !["Machine"] = "s1"]
      /\ UNCHANGED << init, menu, term, gl, cp, opc, water, p, o, w, okPressed, 
                      stack >>

s2 == /\ pc["Machine"] = "s2"
      /\ gl' = TRUE
      /\ term' = TRUE
      /\ \/ /\ pc' = [pc EXCEPT !["Machine"] = "s2"]
         \/ /\ pc' = [pc EXCEPT !["Machine"] = "s0"]
         \/ /\ pc' = [pc EXCEPT !["Machine"] = "s3"]
         \/ /\ pc' = [pc EXCEPT !["Machine"] = "s4"]
      /\ UNCHANGED << init, menu, cp, opc, water, p, o, w, nog, glassRemoved, 
                      okPressed, stack >>

s3 == /\ pc["Machine"] = "s3"
      /\ term' = FALSE
      /\ cp' = TRUE
      /\ \/ /\ stack' = [stack EXCEPT !["Machine"] = << [ procedure |->  "NoCoffee",
                                                          pc        |->  "s1" ] >>
                                                      \o stack["Machine"]]
            /\ pc' = [pc EXCEPT !["Machine"] = "s5"]
         \/ /\ pc' = [pc EXCEPT !["Machine"] = "s8"]
            /\ stack' = stack
      /\ UNCHANGED << init, menu, gl, opc, water, p, o, w, nog, glassRemoved, 
                      okPressed >>

s8 == /\ pc["Machine"] = "s8"
      /\ cp' = FALSE
      /\ opc' = TRUE
      /\ pc' = [pc EXCEPT !["Machine"] = "s4"]
      /\ UNCHANGED << init, menu, term, gl, water, p, o, w, nog, glassRemoved, 
                      okPressed, stack >>

s4 == /\ pc["Machine"] = "s4"
      /\ water' = TRUE
      /\ opc' = FALSE
      /\ pc' = [pc EXCEPT !["Machine"] = "s7"]
      /\ UNCHANGED << init, menu, term, gl, cp, p, o, w, nog, glassRemoved, 
                      okPressed, stack >>

s7 == /\ pc["Machine"] = "s7"
      /\ water' = FALSE
      /\ w' = TRUE
      /\ glassRemoved = TRUE
      /\ glassRemoved' = FALSE
      /\ gl' = FALSE
      /\ pc' = [pc EXCEPT !["Machine"] = "s0"]
      /\ UNCHANGED << init, menu, term, cp, opc, p, o, nog, okPressed, stack >>

Machine == s0 \/ s1 \/ s9 \/ s2 \/ s3 \/ s8 \/ s4 \/ s7

in == /\ pc["User"] = "in"
      /\ init' = TRUE
      /\ pc' = [pc EXCEPT !["User"] = "cyc"]
      /\ UNCHANGED << menu, term, gl, cp, opc, water, p, o, w, nog, 
                      glassRemoved, okPressed, stack >>

cyc == /\ pc["User"] = "cyc"
       /\ \/ /\ pc' = [pc EXCEPT !["User"] = "setGlass"]
          \/ /\ pc' = [pc EXCEPT !["User"] = "getGlass"]
       /\ UNCHANGED << init, menu, term, gl, cp, opc, water, p, o, w, nog, 
                       glassRemoved, okPressed, stack >>

setGlass == /\ pc["User"] = "setGlass"
            /\ nog = TRUE
            /\ nog' = FALSE
            /\ pc' = [pc EXCEPT !["User"] = "cyc"]
            /\ UNCHANGED << init, menu, term, gl, cp, opc, water, p, o, w, 
                            glassRemoved, okPressed, stack >>

getGlass == /\ pc["User"] = "getGlass"
            /\ w = TRUE
            /\ w' = FALSE
            /\ glassRemoved' = TRUE
            /\ pc' = [pc EXCEPT !["User"] = "in"]
            /\ UNCHANGED << init, menu, term, gl, cp, opc, water, p, o, nog, 
                            okPressed, stack >>

User == in \/ cyc \/ setGlass \/ getGlass

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Machine \/ User
           \/ (\E self \in ProcSet: NoCoffee(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Machine) /\ WF_vars(NoCoffee("Machine"))
        /\ WF_vars(User)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
