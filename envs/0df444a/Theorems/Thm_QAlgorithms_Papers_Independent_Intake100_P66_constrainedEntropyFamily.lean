-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P66_constrainedEntropyFamily
-- name    : QAlgorithms.Papers.Independent.Intake100.P66.constrainedEntropyFamily
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:12:15.898626+00:00
-- url     : https://prove2.me/theorems/b23a55b3-458f-4c4d-9a86-c444aee81855
-- title:
--   The infinite constrained quantum entropy family
-- statement:
--   Let $n\ge1$ be an integer. Let $\rho$ be a density operator (positive semidefinite with trace one) on the tensor product of distinct finite-dimensional complex systems $A,B,C,X_1,\ldots,X_n$, each of positive dimension; dimension one is allowed. For any subsystem $J$, let $S(J)=S(\operatorname{Tr}_{J^c}\rho)$ be its von Neumann entropy in bits, with $S(\varnothing)=0$ and $0\log0=0$. For disjoint subsystems, write $I(U:V)=S(U)+S(V)-S(UV)$ and $I(U:V\mid W)=S(UW)+S(VW)-S(W)-S(UVW)$. Assume
--   $$I(A:C\mid B)=I(B:C\mid A)=0.$$
--
--   Then
--   $$S(X_1\cdots X_n)+(n-1)I(AB:C)\le\sum_{i=1}^n S(X_i)+\sum_{i=1}^n I(A:B\mid X_i).$$
--   This gives the constrained family for actual quantum marginal entropies; the case $n=1$ is strong subadditivity.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, PDF p. 3, Theorem 1, §III, equation (10): the infinite constrained quantum entropy family

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Theorem 1, (9)--(10): the infinite constrained entropy family.
No purity, block decomposition, measured state, or classicality is assumed. -/
theorem constrainedEntropyFamily (n : ℕ) (hn : 1 ≤ n) (d : entropyParty n → ℕ)
    (hd : ∀ j, 0 < d j) (rho : Matrix (entropyProductBasis d) (entropyProductBasis d) ℂ)
    (hrho : IsDensityMatrix rho)
    (hAC : evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (entropyOfSubset d rho) = 0)
    (hBC : evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (entropyOfSubset d rho) = 0) :
    0 ≤ evaluateEntropyForm (standardFamily n) (entropyOfSubset d rho) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P66

end
