-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_realignment_tensor_moments
-- name    : QAlgorithms.Papers.Independent.Information100.P19.realignment_tensor_moments
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:51:48.746829+00:00
-- url     : https://prove2.me/theorems/1dea19c1-8329-4bae-b3cf-dd306404aa74
-- title:
--   Proposition 5.3
-- statement:
--   For a Hermitian bipartite operator $X$ in arbitrary positive finite local dimensions and $m\ge1$, let $s_i$ be the singular values of its realignment. Then
--   $$r_m(X)=\operatorname{Tr}[(R(X)R(X)^*)^m]=\sum_i s_i^{2m}=\operatorname{Tr}_{\alpha_m,\beta_m}(X),$$
--   where $\alpha_m=(1\ 2m)(2\ 3)\cdots(2m-2\ 2m-1)$ and $\beta_m=(1\ 2)(3\ 4)\cdots(2m-1\ 2m)$. Row-space zero padding has no effect for $m\ge1$. This identifies the moments as tensor invariants.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 29, Proposition 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 5.3; arXiv:2609.29471v1, PDF pp.29, 30. -/
theorem realignment_tensor_moments (m : ℕ) (hm : 1 ≤ m) (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (X : Bip a b) (hX : X.IsHermitian) :
    rMoment X m = ((singularSpectrum (realign X)).map (fun s => s^(2*m))).sum ∧
    ((rMoment X m : ℝ) : ℂ) = tensorTrace (alphaPerm m,betaPerm m) X := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
