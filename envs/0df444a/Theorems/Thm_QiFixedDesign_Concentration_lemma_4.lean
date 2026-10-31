-- Prove2me | Theorems.Thm_QiFixedDesign_Concentration_lemma_4
-- name    : QiFixedDesign.Concentration.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:52.250027+00:00
-- url     : https://prove2.me/theorems/51d6211c-ddf8-4f27-b33c-dd1fe2527fb2
-- title:
--   Lemma 4 — variance bound from the light-tail coefficients
-- statement:
--   Let $\mu$ be a real Borel probability law of mean zero. Suppose $a>1$, $A>1$ and $\int e^{|u|^a}\,\mu(du)=A<\infty$. Then its variance satisfies
--   $$\sigma^2=\int u^2\,\mu(du)\le (2(A-1))^{1/a}.$$
--   The numerical constant and exponent are exactly those of (33). The variance is a nonnegative extended integral, whose finiteness follows from the exponential-moment assumption.
--
--   Differences from the source:
--   - encoding: A is the finite exponential moment and innovations have mean zero → a nonnegative extended integral equals the finite real A, and the real first integral is zero; reason: light tails guarantee first and second integrability, so no default-zero integral changes an instance
--   - encoding: the variance of the mean-zero innovation → the nonnegative extended integral of its square; reason: mean zero identifies the second moment with variance and an infinite moment cannot turn into zero
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, Lemma 4, (33), PDF/printed p. 16

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_LightTail

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

theorem lemma_4 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a A : ℝ) (hTail : LightTail μ a A) (hMean : ∫ u, u ∂μ = 0) :
    (∫⁻ u, ENNReal.ofReal (u ^ 2) ∂μ) ≤ ENNReal.ofReal (kappa a A) := by sorry

end QiFixedDesign.Concentration
