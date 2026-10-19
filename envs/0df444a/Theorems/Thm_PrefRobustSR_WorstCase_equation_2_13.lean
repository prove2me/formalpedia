-- Prove2me | Theorems.Thm_PrefRobustSR_WorstCase_equation_2_13
-- name    : PrefRobustSR.WorstCase.equation_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:26.554603+00:00
-- url     : https://prove2.me/theorems/966b3486-bb45-4fbf-95f2-cdc47d9a9a80
-- title:
--   Equation (2.13), p. 7: robust risk bounds individual risks
-- statement:
--   Let $L\subseteq\mathcal L$ and let $Z$ be integrable under the probability measure $P$. The common cash requirement is at least the worst individual cash requirement:
--   $$
--   \sup_{l\in L}SR_l^P(Z)\le SR_L^P(Z).
--   $$
--   This is one direction of the representation identity (2.9), including the possible infinite values.
--
--   **Formalization Note** The paper's $\mathcal L_p$ condition is expressed here as integrability, which it implies. The inequality also covers $L=\varnothing$ in the extended reals.
-- source:
--   Delage, Guo & Xu, Shortfall risk models when information of loss function is incomplete, preprint dated April 25, 2018 (later article DOI: https://doi.org/10.1287/opre.2021.2212; numbering follows the preprint), p. 7, (2.13)

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

namespace PrefRobustSR.WorstCase

open MeasureTheory

/-- Equation (2.13), p. 7: the robust cash requirement bounds every individual one. -/
theorem equation_2_13 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (ℝ → ℝ)) (hL : L ⊆ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) :
    (⨆ l ∈ L, SR P l Z) ≤ SRL P L Z := by sorry

end PrefRobustSR.WorstCase
