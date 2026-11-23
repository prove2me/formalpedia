-- Prove2me | Theorems.Thm_WeightedMajority_Shifting_Supplement_theorem_6_3
-- name    : WeightedMajority.Shifting.Supplement.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:56:17.954173+00:00
-- url     : https://prove2.me/theorems/9c22bcf0-f82d-4012-bef7-cf21f1d9a3d7
-- title:
--   Theorem 6.3 — conditional multiplicative tail bound for WMR
-- statement:
--   Let WMR run for $t$ trials with binary labels on a probability space. Pool predictions lie in $[0,1]$, $0\le\beta<1$, initial weights are positive and updates obey (5.1). Let $m$ count the master's mistakes and let $G$ be the sigma algebra of the full external prediction/label sequence. Assume strong independence, including conditioning on previous master predictions. Let $a,b$ be $G$-measurable real random variables with $0<a\le1$ almost surely and $P[m\mid G]\le b$ almost surely. Then
--
--   $$P\bigl(m>(1+a)b\mid G\bigr)\le\exp(-a^2b/3)\quad\text{almost surely}.$$
--
--   This controls fluctuations about any external-data-dependent upper bound on the conditional mean. The conclusion is the conditional expectation of the tail-event indicator. Neither $t>0$ nor $b>0$ is assumed.
--
--   **Formalization Note** The source's normalized prediction is defined on runs with positive pre-trial total weight almost surely; no positivity is imposed after the last update.
--
--   Differences from the source:
--   - encoding: positive trial indices and conditional tail probability → zero-based trials and conditional expectation of a real indicator; reason: the event and conditioning sigma algebra are unchanged
--   - reading: WMR with normalized weighted prediction → positive total weight before every requested prediction, almost surely; reason: the ratio on p. 232 is undefined at zero total; the final total may still vanish
--   - generalization: 0 < a ≤ 1 → 0 < a ≤ 1 almost surely; reason: the hypothesis is only needed off a null set, so every source instance is covered
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), DOI 10.1006/inco.1994.1009, p. 242, Theorem 6.3

import Definitions.Def_WeightedMajority_Shifting_Supplement_StrongIndependence

open MeasureTheory

namespace WeightedMajority.Shifting.Supplement

theorem theorem_6_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (t : ℕ) (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ)
    (ρ lam : ℕ → Ω → ℝ)
    (hrun : WeightedMajority.Randomized.IsWMRModel t β w1 F x ρ lam)
    (hpositive : ∀ j < t, ∀ᵐ ω ∂P,
      0 < WeightedMajority.Randomized.totalWeight w1 F x ρ j ω)
    (hind : StrongIndependence P t w1 F x ρ lam)
    (a b : Ω → ℝ) (ha : Measurable[external t x ρ] a)
    (hb : Measurable[external t x ρ] b)
    (ha_range : ∀ᵐ ω ∂P, 0 < a ω ∧ a ω ≤ 1)
    (hmean : ∀ᵐ ω ∂P, P[WeightedMajority.Randomized.mistakes t lam ρ | external t x ρ] ω ≤ b ω) :
    ∀ᵐ ω ∂P,
      P[(fun z => if WeightedMajority.Randomized.mistakes t lam ρ z > (1 + a z) * b z
        then (1 : ℝ) else 0) | external t x ρ] ω ≤ Real.exp (-(a ω) ^ 2 * b ω / 3) := by sorry

end WeightedMajority.Shifting.Supplement
