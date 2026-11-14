-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_wasserstein_le_measurable_seed_bit_changes
-- name    : StabilityDichotomies.Solvability.wasserstein_le_measurable_seed_bit_changes
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:41:09.694954+00:00
-- url     : https://prove2.me/theorems/5ee66d00-1ba1-4bd0-9a15-cf47db590074
-- title:
--   A measurable shared seed bounds Wasserstein distance by bit-disagreement probabilities
-- statement:
--   Let $f$ and $g$ be measurable maps from a common probability space into assignments on a finite set of Boolean variables. Their output laws satisfy
--   $$W_1(\mathcal L(f),\mathcal L(g))\le\sum_v\Pr[f(v)\ne g(v)].$$
--   This is the shared-randomness coupling bound needed for the continuous priority, cutoff, and shift seeds in Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, coupling and Hamming-distance bound.

import Definitions.Def_StabilityDichotomies_Solvability_Stability
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.wasserstein_le_measurable_seed_bit_changes {V Ω : Type} [Fintype V] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → V → Bool)
    (hf : Measurable f) (hg : Measurable g) :
    letI : IsProbabilityMeasure (Measure.map f μ) := Measure.isProbabilityMeasure_map hf.aemeasurable
    letI : IsProbabilityMeasure (Measure.map g μ) := Measure.isProbabilityMeasure_map hg.aemeasurable
    wasserstein ((Measure.map f μ).toPMF) ((Measure.map g μ).toPMF) ≤
      ∑ v : V, (μ {ω | f ω v ≠ g ω v}).toReal := by
  sorry
