/- @@@
JACK BOWERS

#1. Suppose P and Q are any propositions.

#1.A: State and prove the conjecture that,
*and* implies *equivalence*. In other words,
if for any propositions, X and Y, X ∧ Y is
true, then it must be that X ↔ Y is as well.
Call your theorem andImpEquiv.
@@@ -/


-- ANSWER
theorem andImpEquiv {P Q : Prop} : P ∧ Q → (P ↔ Q) :=
  fun ⟨hp, hq⟩ =>
    Iff.intro (fun _ => hq) (fun _ => hp)


/- @@@
#2: Give the proof in #1 in English. To do this,
just explain clearly what assumptions you make or
use at each step and what inference rules you use
to make progress at each step. We get you started:

-- ANSWER
Proof: To prove this *implication* we'll use the
introduction rule for →. So *assume* the premise
is true. What remains to be proved is that, in this
context,  and we will then show that, in that
context, the conclusion must be true as well. So
assume P ∧ Q is true. The conclusion to be proved
is an equivalence.

To prove that (P ∧ Q) → (P ↔ Q), assume that P ∧ Q is true.
From this assumption, we know P is true and Q is true.

To show an equivalence (↔), we must prove both directions:
Assume P. Then Q follows because Q is already true.
Assume Q. Then P follows because P is already true.
Thus, both directions hold, so P ↔ Q is true.
@@@ -/


/- @@@
#3: Use axiom declarations to represent this world.

- X is a proposition
- Y is a proposition
- X ∧ Y is true

Once you've done that, in a #check command, apply
the general theorem we just proved to prove that X
is equivalent to Y.

Do not just copy the proof. The whole point is to
reinforce the idea that one you've proved a theorem
you can use it (by applying it) to prove any special
case (here involving X and Y) of the general claim.
@@@ -/

-- Answer
axiom X : Prop
axiom Y : Prop
axiom xytrue : X ∧ Y

#check andImpEquiv xytrue



/- @@@
#4: Something About False

Recall from class discussion that the proposition,
in Lean, called False, has no proofs at all. That
is what makes it false. Assuming that there is one
assumes something that's impossible. The crucial
conclusion to draw is *not* that the impossible is
suddenly possible, but that the *assumption* itself
must be wrong. Therefore, if at any point in trying
to prove something we can derive a proof of False,
that means we're in a situation that can't actually
happen. So we really don't have to finish the proof!

For example, suppose  K is some unknown proposition.
When we say that (False → K) is true, we are *not*
saying that *K* is true; we're saying that once you
assume or can derive a proof of False, you know you
are in a case that can never happen, so you can just
"bail out" and not worry about constructing a proof
of K, no matter what proposition it is. The keyword
*nomatch* in Lean applied to any proof of false does
exactly bail one of of an impossible case.

Here's a formal proof of it. We assume K is any
proposition, then we prove False → K. To prove
this implication, we assume we're given f, a proof
of false. In any other situation, for *exFalsoK*
to be defined, we'd *have to* return some value of
type K. Here we don't even know what that type is.
And yet the function is well-defined, and as such
*proves* the implication, *False → K*. The trick
of course, is that as soon as we have a proof of
false in (or derivable given) our context, then we
can *bail out* and Lean will accept the definition.
Lean's *nomatch* construct will bail you out as long
as it's applied to a proof of false, which is the
evidence Lean needs to know it's ok to accept the
definition.
@@@ -/

-- ANSWER
theorem exFalsoK {K : Prop} : False → K :=
  fun f => nomatch f

/- @@@
Why is it safe to accept this definition? What do we
know that's special about *exFalsoK* that makes it ok?

-- ANSWER:
Because False has no proofs. The function "exFalsoK" can never actually be applied to a real argument.
This defines it is safe, as it will never be used in a way that leads to inconsistency.
@@@ -/


/- @@@
#5 In Lean, state and prove the proposition that is
P and Q are arbitrary propositions, then False *and*
P implies Q.
@@@-/

-- ANSWER
theorem falseAndP_implies_Q {P Q : Prop} : False ∧ P → Q :=
  fun ⟨f, _⟩ => exFalsoK f

/- @@@
Write a short paragraph stating the proposition to be
proved and the proof of it -- in English.

-- ANSWER
Suppose False ∧ P is true. Then False must be true.
From a proof of False, any proposition follows (exFalsoK).
Thus Q follows.
@@@ -/


/- @@@
#6 State and prove the proposition that False → False.
Give both formal and English (natural language) proofs.


-- ANSWER
Suppose False is true. Then we already have a proof of False.
Thus False → False holds by returning the same proof.
@@@ -/


-- ANSWER
theorem falseImpFalse : False → False :=
  fun f => f
