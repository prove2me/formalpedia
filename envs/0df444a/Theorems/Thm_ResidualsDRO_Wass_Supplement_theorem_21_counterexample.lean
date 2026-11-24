-- Prove2me | Theorems.Thm_ResidualsDRO_Wass_Supplement_theorem_21_counterexample
-- name    : ResidualsDRO.Wass.Supplement.theorem_21_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:45:33.481451+00:00
-- url     : https://prove2.me/theorems/c489ecf7-756e-4dac-8660-a4d72520fabd
-- title:
--   Theorem 21 (corrected: scalar refutation) — failure of eventual certification
-- statement:
--   Theorem 21 fails in its printed one-dimensional domain. Let U_i be i.i.d. uniform [0,1], take an exact constant regression f*=fhat_n=1/2, zero-mean uniform residuals, a singleton decision set, response range [0,1], and cost c(z,y)=y. Choose α_n=(n+2)^{-2}, κ_n(α)=n^{-2}, θ=3/4 and any C>0 in (13). All printed assumptions hold, and the exact sample-robust value is
--
--   $$\widehat v_n=\frac1n\sum_{i=1}^n\min\{1,U_i+2n^{-2}+Cn^{-3/4}\},\qquad g(\widehat z_n)=\tfrac12.$$
--
--   The counterexample target states
--
--   $$\mathbb P\{\exists N,\ \forall n\ge N:\ \tfrac12\le\widehat v_n\}=0.$$
--
--   Thus it contradicts even the sample-path-dependent eventual time supplied by the proof. The scalar law of the iterated logarithm establishes recurring sample-mean deficits larger than the radius; the complete argument, source anchors and connection with (8) are in DISPROOF.md. This is an unproved Lean counterexample target, not a claim of an already verified LIL proof.
--
--   Differences from the source:
--
--   - correction: Theorem 21 asserts eventual certification for all dimensions with radius (13) → a dimension-one uniform-response counterexample has probability zero of eventual certification; reason: p. 26 Lemma 19 has an invalid log(n)/n scale in dimension one; p. 27 allows θ=3/4; the scalar LIL forces infinitely many failures (DISPROOF.md)
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, p. 27, Theorem 21

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Infinity

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

/-- Counterexample to Theorem 21, p. 27, in dimension one: θ=3/4, exact regression, uniform Y, c(z,y)=y. The law of the iterated logarithm gives failure infinitely often. See DISPROOF.md. -/
theorem theorem_21_counterexample
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℕ → Ω → ℝ) (hiid : ProbabilityTheory.iIndepFun U P)
    (hmeas : ∀ i, Measurable (U i))
    (hlaw : ∀ i, Measure.map (U i) P = volume.restrict (Set.Icc (0 : ℝ) 1))
    (C : ℝ) (hC : 0 < C) :
    P {ω | ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
      (1 / 2 : ℝ) ≤ uniformRobustValue (counterRadius C n) (fun i : Fin n => U i ω)} = 0 := by sorry

end ResidualsDRO.Wass.Supplement
