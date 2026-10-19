-- Prove2me | Theorems.Thm_StochSeedEval_Hajek_consistency
-- name    : StochSeedEval.Hajek.consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:31.962099+00:00
-- url     : https://prove2.me/theorems/d874ea1f-7c86-41e7-a30c-5341c9a0c914
-- title:
--   Proof of Proposition 2, p. 39 — corrected almost-sure consistency of the Hájek estimator
-- statement:
--   Let $\widetilde\tau_N$ be the difference of the two separately normalized weighted outcome averages from equation (7). If the design covers the support of both strategies, the weighted outcomes have finite first moments, and the observed seed sets are independent with common design law, then
--
--   $$\widetilde\tau_N\longrightarrow\tau_{\mathrm{sp}}=\mu_A-\mu_B\qquad\text{almost surely}.$$
--
--   This is the consistency part of corrected Proposition 2. It needs only first moments; finite second moments enter the normal limit, not this claim.
--
--   **Formalization Note.** Zero finite sample denominators use Lean's total division convention. They do not alter the stated almost-sure limit.
-- source:
--   Chin, Eckles & Ugander, Evaluating Stochastic Seeding Strategies in Networks, arXiv:1809.09561v3, p. 39, proof of Proposition 2, consistency sentence (corrected using full positivity)

import Mathlib
import Definitions.Def_StochSeedEval_Hajek_Estimators

open MeasureTheory ProbabilityTheory Filter Topology

namespace StochSeedEval.Hajek

/-- Corrected consistency claim in the proof of Proposition 2, p. 39. -/
theorem consistency
    {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hAy : Integrable (fun s => weightA pA pD s * y s) pD.toMeasure)
    (hBy : Integrable (fun s => weightB pB pD s * y s) pD.toMeasure)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) :
    ∀ᵐ ω ∂P, Tendsto (fun N => hajek pA pB pD y S N ω) atTop (𝓝 (contrast pA pB y)) := by sorry

end StochSeedEval.Hajek
