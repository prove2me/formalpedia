-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P66_constrainedEntropyFamily_cAsX
-- name    : QAlgorithms.Papers.Independent.Intake100.P66.constrainedEntropyFamily_cAsX
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:16:26.231967+00:00
-- url     : https://prove2.me/theorems/ab012632-2041-4d86-a8a0-dbed150b49fa
-- title:
--   The variant allowing C as an X party
-- statement:
--   Let $n\ge1$ be an integer. Let $\rho$ be a density operator (positive semidefinite with trace one) on the tensor product of distinct finite-dimensional complex systems $A,B,C,X_1,\ldots,X_n$, each of positive dimension; dimension one is allowed. For any subsystem $J$, let $S(J)=S(\operatorname{Tr}_{J^c}\rho)$ be its von Neumann entropy in bits, with $S(\varnothing)=0$ and $0\log0=0$. For disjoint subsystems, write $I(U:V)=S(U)+S(V)-S(UV)$ and $I(U:V\mid W)=S(UW)+S(VW)-S(W)-S(UVW)$. Assume
--   $$I(A:C\mid B)=I(B:C\mid A)=0.$$
--
--   Then
--   $$\sum_{i=1}^n I(A:B\mid X_i)+\sum_{i=1}^n S(X_i)+I(A:B\mid C)+S(C)-S(CX_1\cdots X_n)-nI(AB:C)\ge0.$$
--   This is the additional family obtained by including $C$ once among the X parties in the construction. The term $I(A:B\mid C)$ need not vanish.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, PDF p. 10, Theorem 5, §V, equation (47): allow C as an X party

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10, Theorem 5, (47): C is included once as an additional X party.
I(A:B|C) is a conclusion term, not an extra zero constraint. -/
theorem constrainedEntropyFamily_cAsX (n : ℕ) (hn : 1 ≤ n) (d : entropyParty n → ℕ)
    (hd : ∀ j, 0 < d j) (rho : Matrix (entropyProductBasis d) (entropyProductBasis d) ℂ)
    (hrho : IsDensityMatrix rho)
    (hAC : evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (entropyOfSubset d rho) = 0)
    (hBC : evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (entropyOfSubset d rho) = 0) :
    0 ≤ evaluateEntropyForm (cAsXForm {entropyLabelA} {b} {c} standardX) (entropyOfSubset d rho) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P66

end
