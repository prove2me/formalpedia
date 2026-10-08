-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch4_matrix_series
-- name    : TroppMatrixConcentration.ch4_matrix_series
-- status  : Open
-- author  : @tc
-- created : 2026-10-07T13:47:01.472557+00:00
-- url     : https://prove2.me/theorems/ba040093-f86b-4552-b6c5-db4320f287cb
-- title:
--   Theorem 4.1.1 — Matrix Gaussian and Rademacher series
-- statement:
--   Let $B_k$ be a finite family of fixed complex $m\times n$ matrices, with $m,n\ge1$. On an arbitrary probability space let $g_k$ be independent measurable real random variables, either all standard normal or all Rademacher. Put $Z=\sum_k g_k B_k$ and define the actual second-moment statistic $v=\max\{\|\mathbb E ZZ^*\|,\|\mathbb E Z^*Z\|\}$. Then
--   $$v=\max\left\{\left\|\sum_k B_kB_k^*\right\|,\left\|\sum_k B_k^*B_k\right\|\right\},$$
--   $$\mathbb E\|Z\|\le\sqrt{2v\log(m+n)},$$
--   $$\mathbb P\{\|Z\|\ge t\}\le(m+n)\exp(-t^2/(2v))\qquad(t\ge0).$$
--   All norms are Euclidean operator norms. At $v=0$ the tail right side is $m+n$ for $t=0$ and zero for $t>0$. The finite family may be empty. Both scalar distributions are included in the same theorem via a disjunction on the whole family's laws.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 4.1.1, equations (4.1.2–6), printed p. 42.

import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws
import Definitions.Def_TroppMatrixConcentration_dilation

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace TroppMatrixConcentration

theorem ch4_matrix_series {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n N : ℕ} [NeZero m] [NeZero n]
    (B : Fin N → Matrix (Fin m) (Fin n) ℂ)
    (g : Fin N → Ω → ℝ) (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ)
    (hLaw : (∀ k, standardGaussianLaw μ (g k)) ∨ (∀ k, rademacherLaw μ (g k))) :
    let Z := fun ω => ∑ k, g k ω • B k
    let v := rectSecondMoment μ Z
    v = max (spectralNorm (∑ k, B k * (B k).conjTranspose))
      (spectralNorm (∑ k, (B k).conjTranspose * B k)) ∧
    (∫ ω, spectralNorm (Z ω) ∂μ) ≤ Real.sqrt (2 * v * Real.log (m + n)) ∧
    ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
      gaussianSeriesTail (m + n) v t := by sorry

end TroppMatrixConcentration
