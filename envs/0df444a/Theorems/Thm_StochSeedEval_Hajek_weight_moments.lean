-- Prove2me | Theorems.Thm_StochSeedEval_Hajek_weight_moments
-- name    : StochSeedEval.Hajek.weight_moments
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:19.265476+00:00
-- url     : https://prove2.me/theorems/9565e6e3-66aa-4cae-bb34-69f5f15deb26
-- title:
--   Proof of Proposition 2, p. 40 — corrected weight moment identities
-- statement:
--   Let $p_A$ and $p_B$ be strategy distributions on a countable seed space, $p_\Delta$ a design distribution, and $y$ a real outcome. Suppose the design assigns positive probability wherever either strategy does, and that $w_Ay$ and $w_By$ are integrable under the design. Then the four coordinates of the population mean of the sample-average vector are
--
--   $$\mathbb E_\Delta[w_A]=1,\qquad \mathbb E_\Delta[w_B]=1,\qquad \mathbb E_\Delta[w_Ay]=\mu_A,\qquad \mathbb E_\Delta[w_By]=\mu_B.$$
--
--   These identities identify the center of the joint limit theorem and the two denominators of the Hájek estimator.
--
--   **Formalization Note.** This is corrected relative to the paper's Assumption 1: requiring positive design probability only where $p_A\ne p_B$ does not ensure that either expected weight is one.
-- source:
--   Chin, Eckles & Ugander, Evaluating Stochastic Seeding Strategies in Networks, arXiv:1809.09561v3, p. 40, proof of Proposition 2, β := E[β̂] display (corrected using full positivity)

import Mathlib
import Definitions.Def_StochSeedEval_Hajek_Estimators

open MeasureTheory

namespace StochSeedEval.Hajek

/-- Corrected moment identity in the proof of Proposition 2, p. 40. -/
theorem weight_moments
    {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hAy : Integrable (fun s => weightA pA pD s * y s) pD.toMeasure)
    (hBy : Integrable (fun s => weightB pB pD s * y s) pD.toMeasure) :
    (∫ s, weightA pA pD s ∂pD.toMeasure) = 1 ∧
    (∫ s, weightB pB pD s ∂pD.toMeasure) = 1 ∧
    (∫ s, weightA pA pD s * y s ∂pD.toMeasure) = meanA pA y ∧
    (∫ s, weightB pB pD s * y s ∂pD.toMeasure) = meanB pB y := by sorry

end StochSeedEval.Hajek
