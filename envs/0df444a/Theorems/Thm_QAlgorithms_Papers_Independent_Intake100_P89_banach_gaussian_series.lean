-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_banach_gaussian_series
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.banach_gaussian_series
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:41:34.279982+00:00
-- url     : https://prove2.me/theorems/e097abb9-1981-46c7-931a-22c28ea86bbf
-- title:
--   Theorem 4.2: Banach Gaussian series
-- statement:
--   Let $h_i$ be deterministic vectors in a real separable Banach space, and let $Z_i$ be iid standard normals. Suppose the ordered series $\sum_iZ_ih_i$ converges almost surely to a Borel version $W$. Assume that an $\ell^2$ coefficient sequence whose deterministic series converges to zero must itself be zero. Then all deterministic $\ell^2$ series converge in $B$, $W$ is centered Gaussian, and
--   $$H_W=\left\{\sum_iw_ih_i:w\in\ell^2\right\},\qquad\left\|\sum_iw_ih_i\right\|_H^2=\sum_iw_i^2.$$
--   Deterministic convergence is a conclusion, not an extra assumption.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 12, Theorem 4.2: Banach Gaussian series

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section MoreResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- Theorem 4.2: Banach Gaussian series, arXiv:0805.3252v1, PDF p.12.
The malformed printed w in l2 < infinity means w in l2. Random convergence uses ordered partial sums, not an unconditional HasSum. W is a Borel version of the a.s. limit. -/
theorem banach_gaussian_series
{B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [TopologicalSpace.SeparableSpace B]
    (h : ℕ → B) (Z : ℕ → Omega → ℝ) (hZ : StandardNormals P Z)
    (W : Omega → B) (hW : @Measurable Omega B _ (borel B) W)
    (hlim : ∀ᵐ o ∂P, Tendsto (fun n => ∑ i ∈ Finset.range n, Z i o • h i)
      atTop (𝓝 (W o)))
    (hunique : ∀ w : ℕ → ℝ, Summable (fun i => (w i) ^ 2) →
      Tendsto (fun n => ∑ i ∈ Finset.range n, w i • h i) atTop (𝓝 0) →
      ∀ i, w i = 0) :
    BorelCenteredGaussianElement P W ∧
    (∀ w : ℕ → ℝ, Summable (fun i => (w i) ^ 2) → Summable (fun i => w i • h i)) ∧
    banachRKHS P W = {b | ∃ w : ℕ → ℝ,
      Summable (fun i => (w i) ^ 2) ∧ b = series h w} ∧
    ∀ w : ℕ → ℝ, Summable (fun i => (w i) ^ 2) →
      banachNorm P W (series h w) ^ 2 = ∑' i, (w i) ^ 2 := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
