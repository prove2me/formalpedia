-- Prove2me | Theorems.Thm_StochSeedEval_Hajek_sample_averages
-- name    : StochSeedEval.Hajek.sample_averages
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:12.223996+00:00
-- url     : https://prove2.me/theorems/069c1b43-781d-44a1-b57d-9254204b9033
-- title:
--   Proof of Proposition 2, p. 39 — almost-sure limits of the four sample averages
-- statement:
--   Under full positivity, integrable weighted outcomes, and an independent sequence of seed sets with common design law $p_\Delta$, the four sample averages used in the proof of Proposition 2 have the simultaneous almost-sure limits
--
--   $$\bar w_{A,N}\to1,\qquad\bar w_{B,N}\to1,\qquad\overline{w_Ay}_N\to\mu_A,\qquad\overline{w_By}_N\to\mu_B.$$
--
--   Here each average uses the first $N$ observed seed sets. This records the exact centers needed to normalize the estimator, rather than leaving the limits as unnamed expectations.
--
--   **Formalization Note.** The sample is indexed from zero in Lean, and the conclusion is almost sure convergence of all four sequences on the same event.
-- source:
--   Chin, Eckles & Ugander, Evaluating Stochastic Seeding Strategies in Networks, arXiv:1809.09561v3, p. 39, proof of Proposition 2, sample-average displays and consistency sentence

import Mathlib
import Definitions.Def_StochSeedEval_Hajek_Estimators

open MeasureTheory ProbabilityTheory Filter Topology

namespace StochSeedEval.Hajek

/-- Four sample averages in the proof of Proposition 2, p. 39. -/
theorem sample_averages
    {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hAy : Integrable (fun s => weightA pA pD s * y s) pD.toMeasure)
    (hBy : Integrable (fun s => weightB pB pD s * y s) pD.toMeasure)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) :
    ∀ᵐ ω ∂P,
      Tendsto (fun N => sampleAverage S (weightA pA pD) N ω) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun N => sampleAverage S (weightB pB pD) N ω) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun N => sampleAverage S (fun s => weightA pA pD s * y s) N ω)
        atTop (𝓝 (meanA pA y)) ∧
      Tendsto (fun N => sampleAverage S (fun s => weightB pB pD s * y s) N ω)
        atTop (𝓝 (meanB pB y)) := by sorry

end StochSeedEval.Hajek
