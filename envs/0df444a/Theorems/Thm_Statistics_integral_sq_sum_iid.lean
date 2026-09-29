-- Prove2me | Theorems.Thm_Statistics_integral_sq_sum_iid
-- name    : Statistics.integral_sq_sum_iid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T15:19:17.770041+00:00
-- url     : https://prove2.me/theorems/97658c89-d26b-4d7f-830b-4cbc1221d595
-- title:
--   Second moment of a sum over an i.i.d. sample
-- statement:
--   **The second moment of a sum over an i.i.d. sample.** Let $\varphi$ be a square-integrable functional with mean zero under a probability measure $\mu$, and let $X_1,\dots,X_T$ be i.i.d. with law $\mu$. Then
--   $$\mathbb E\Bigl[\Bigl(\sum_{i=1}^T \varphi(X_i)\Bigr)^2\Bigr] \;=\; T\;\mathbb E\bigl[\varphi(X_1)^2\bigr].$$
--
--   Expanding the square, the diagonal terms each contribute the second moment and the off-diagonal terms factor by independence into a product of two means, both zero. This is the additivity of variance for independent centred summands, in the form needed to compute the Fisher information of a sample of size $T$ from the information of a single observation.
-- source:
--   Standard; see e.g. R. Durrett, Probability: Theory and Examples, 5th ed., Cambridge 2019, Theorem 2.2.5 (variance of a sum of independent random variables).

import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem Statistics.integral_sq_sum_iid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : ℕ) (φ : Ω → ℝ)
    (hmeas : Measurable φ) (hφ : MemLp φ 2 μ) (hφ0 : ∫ x, φ x ∂μ = 0) :
    ∫ path, (∑ i : Fin T, φ (path i)) ^ 2 ∂(Measure.pi fun _ : Fin T => μ)
      = (T : ℝ) * ∫ x, (φ x) ^ 2 ∂μ := by sorry
