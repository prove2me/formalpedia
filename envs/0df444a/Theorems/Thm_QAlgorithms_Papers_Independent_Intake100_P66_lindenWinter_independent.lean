-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P66_lindenWinter_independent
-- name    : QAlgorithms.Papers.Independent.Intake100.P66.lindenWinter_independent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:17:45.224056+00:00
-- url     : https://prove2.me/theorems/791ec1c9-e234-4cf8-bbe4-fd42c4705bfc
-- title:
--   A four-party witness separating the old Linden–Winter inequality
-- statement:
--   On the four distinct labels $A,B,C,D$, let $e$ be the normalized real set function with values in the order $(\varnothing,A,B,C,D,AB,AC,AD,BC,BD,CD,ABC,ABD,ACD,BCD,ABCD)$ given by
--   $$(0,5,5,2,4,6,5,5,5,5,6,6,6,5,5,4).$$
--   Write $I_e(U:V\mid W)=e(UW)+e(VW)-e(W)-e(UVW)$ and $I_e(U:V)=e(U)+e(V)-e(UV)$. The function satisfies all SSA and WMO instances and the constraints $I_e(A:C\mid B)=I_e(B:C\mid A)=I_e(A:B\mid D)=0$, while
--   $$I_e(C:D)-I_e(AB:C)=-2.$$
--   For a normalized set function $h$, define the three new fixed-label residuals
--   $$R_{46}(h)=I_h(A:B\mid D)+h(D)+I_h(A:B\mid CD)+h(ABCD)-h(ABC)-I_h(AB:C),$$
--   $$R_{47}(h)=I_h(A:B\mid D)+h(D)+I_h(A:B\mid C)+h(C)-h(CD)-I_h(AB:C),$$
--   $$R_{48}(h)=I_h(A:B\mid D)+h(D)+I_h(A:B\mid CD)+h(ABCD)+I_h(A:B\mid C)+h(C)-h(AB)-2I_h(AB:C).$$
--   Each $R_{46}(e),R_{47}(e),R_{48}(e)$ is nonnegative. Consequently the old residual is not a finite nonnegative combination of these three fixed-label forms and arbitrary basic instances, plus any real combination of the three zero-constraint forms. This is a set-function witness of linear independence, without asserting that $e$ is entropic or making a claim about all substitutions of higher-party variants.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, PDF p. 10, §V, unnumbered: the old Linden–Winter inequality is independent of the three new four-party forms

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10, final paragraph of Section V: the printed table satisfies the basic
inequalities and old constraints, violates the old residual, and satisfies the
three new fixed-label forms. Consequently there is no finite linear derivation
of the old form from these three forms, the basics and the old zero constraints. -/
theorem lindenWinter_independent :
    (∀ L : Form (entropyParty 1), QuantumBasic L → 0 ≤ evaluateEntropyForm L oldWitness) ∧
    (∀ Z ∈ oldConstraints, evaluateEntropyForm Z oldWitness = 0) ∧
    evaluateEntropyForm oldForm oldWitness = -2 ∧
    (∀ L : Form (entropyParty 1), NewFourParty L → 0 ≤ evaluateEntropyForm L oldWitness) ∧
    ¬ Derivable {L | QuantumBasic L ∨ NewFourParty L} oldConstraints oldForm := by sorry

end QAlgorithms.Papers.Independent.Intake100.P66

end
