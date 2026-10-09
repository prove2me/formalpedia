-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch6_independent_sum_second_moment
-- name    : TroppMatrixConcentration.ch6_independent_sum_second_moment
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T01:23:56.024143+00:00
-- url     : https://prove2.me/theorems/e7ab591f-f8c3-49dc-9a65-0e84d02a9c01
-- title:
--   Second moment of an independent centered matrix sum: cross terms vanish
-- statement:
--   Let $X_1,\dots,X_N$ be independent measurable random $m\times n$ complex matrices on a probability space, and let $f$ and $g$ be measurable matrix-valued maps (into $a\times b$ and $b\times c$ matrices) such that each $f(X_k)$ and each $g(X_k)$ is square integrable for the spectral norm and $\mathbb E\,f(X_k)=0$ for every $k$. Then
--   $$\mathbb E\Big[\Big(\sum_k f(X_k)\Big)\Big(\sum_k g(X_k)\Big)\Big]=\sum_k \mathbb E\big[f(X_k)\,g(X_k)\big].$$
--   The cross terms $\mathbb E[f(X_j)g(X_k)]$ with $j\ne k$ vanish because $f(X_j)$ and $g(X_k)$ are independent and $f(X_j)$ has mean zero. Taking $f=g=\mathrm{id}$ gives the additivity of the matrix variance of an independent centered Hermitian sum (Tropp, eq. (2.2.5)); taking $f=\mathrm{id}$, $g=(\cdot)^*$ or $f=(\cdot)^*$, $g=\mathrm{id}$ gives the two rectangular variance identities used in the matrix Bernstein inequalities (Tropp, eqs. (6.1.2) and (7.3.2)). Expectations are Bochner integrals with respect to the spectral norm.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Section 2.2.3, equations (2.2.5)-(2.2.6), printed pp. 27-28 (additivity of the variance of an independent sum; the cross terms vanish by independence and zero mean); used in Theorem 6.1.1 eq. (6.1.2), Theorem 6.6.1, and Theorem 7.3.1 eq. (7.3.2).

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch6_independent_sum_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n a b c N : ℕ}
    (X : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ)
    (f : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin a) (Fin b) ℂ)
    (g : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin b) (Fin c) ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hfL2 : ∀ k, MemLp (fun ω => f (X k ω)) 2 μ)
    (hgL2 : ∀ k, MemLp (fun ω => g (X k ω)) 2 μ)
    (hfMean : ∀ k, (∫ ω, f (X k ω) ∂μ) = 0) :
    (∫ ω, (∑ k, f (X k ω)) * (∑ k, g (X k ω)) ∂μ) =
      ∑ k, ∫ ω, f (X k ω) * g (X k ω) ∂μ := by sorry

end TroppMatrixConcentration
