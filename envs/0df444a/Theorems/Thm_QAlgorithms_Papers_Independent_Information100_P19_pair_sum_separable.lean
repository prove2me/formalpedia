-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_pair_sum_separable
-- name    : QAlgorithms.Papers.Independent.Information100.P19.pair_sum_separable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:55:13.459988+00:00
-- url     : https://prove2.me/theorems/7c114557-1c3d-4b6f-b01e-7a805b6641d3
-- title:
--   Proposition 5.7
-- statement:
--   Every unnormalized separable positive bipartite operator $X$, with $t=\operatorname{Tr}X$, satisfies
--   $$2(r_1(X)^2-r_2(X))\le(t^2-r_1(X))^2.$$
--   This is a homogeneous degree-four separability criterion and includes $X=0$.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 31, Proposition 5.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 5.7; arXiv:2609.29471v1, PDF pp.31, 32. -/
theorem pair_sum_separable (a b : ℕ) (ha : 0<a) (hb : 0<b) (X : Bip a b)
    (hX : QAlgorithms.Entanglement.IsSeparablePositive X) :
    2*(rMoment X 1^2-rMoment X 2) ≤ (mass X^2-rMoment X 1)^2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
