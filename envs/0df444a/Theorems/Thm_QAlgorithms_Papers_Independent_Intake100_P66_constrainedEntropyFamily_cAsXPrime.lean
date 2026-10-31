-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P66_constrainedEntropyFamily_cAsXPrime
-- name    : QAlgorithms.Papers.Independent.Intake100.P66.constrainedEntropyFamily_cAsXPrime
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:17:07.841418+00:00
-- url     : https://prove2.me/theorems/62f3c495-634a-4321-9126-e75393893b50
-- title:
--   The purified C-as-X variant
-- statement:
--   Let $n\ge1$ be an integer. Let $\rho$ be a density operator (positive semidefinite with trace one) on the tensor product of distinct finite-dimensional complex systems $A,B,C,X_1,\ldots,X_n$, each of positive dimension; dimension one is allowed. For any subsystem $J$, let $S(J)=S(\operatorname{Tr}_{J^c}\rho)$ be its von Neumann entropy in bits, with $S(\varnothing)=0$ and $0\log0=0$. For disjoint subsystems, write $I(U:V)=S(U)+S(V)-S(UV)$ and $I(U:V\mid W)=S(UW)+S(VW)-S(W)-S(UVW)$. Assume
--   $$I(A:C\mid B)=I(B:C\mid A)=0.$$
--
--   Then
--   $$\sum_{i=1}^n I(A:B\mid X_i)+\sum_{i=1}^n S(X_i)+I(A:B\mid CX_1\cdots X_n)+S(ABCX_1\cdots X_n)+I(A:B\mid C)+S(C)-S(AB)-(n+1)I(AB:C)\ge0.$$
--   This variant combines the C-as-X construction and purification elimination; the displayed state may be mixed.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, PDF p. 10, Theorem 5′, §V, equation (48): purified C-as-X variant

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.10, Theorem 5-prime, (48): -S(AB), not -S(ABC), and coefficient n+1.
The state is arbitrary mixed, despite the purification used in the derivation. -/
theorem constrainedEntropyFamily_cAsXPrime (n : ℕ) (hn : 1 ≤ n) (d : entropyParty n → ℕ)
    (hd : ∀ j, 0 < d j) (rho : Matrix (entropyProductBasis d) (entropyProductBasis d) ℂ)
    (hrho : IsDensityMatrix rho)
    (hAC : evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (entropyOfSubset d rho) = 0)
    (hBC : evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (entropyOfSubset d rho) = 0) :
    0 ≤ evaluateEntropyForm (cAsXPrimeForm {entropyLabelA} {b} {c} standardX) (entropyOfSubset d rho) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P66

end
