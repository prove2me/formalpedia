-- Prove2me | Theorems.Thm_PrefRobustSR_WorstCase_equation_2_12
-- name    : PrefRobustSR.WorstCase.equation_2_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:52.687472+00:00
-- url     : https://prove2.me/theorems/c0ebc658-0a15-498c-ba52-0f0523a4142f
-- title:
--   Equation (2.12), p. 7: robust gap diverges
-- statement:
--   Let $L$ be a nonempty subset of $\mathcal L$, and let $Z$ be integrable under the probability measure $P$. The robust expected-loss gap diverges as the cash amount decreases:
--   $$
--   \lim_{t\to-\infty}\sup_{l\in L}\bigl(\mathbb E_P[l(-Z-t)]-l(0)\bigr)=+\infty.
--   $$
--   Thus sufficiently negative cash amounts cannot satisfy the robust shortfall constraint.
--
--   **Formalization Note** Nonemptiness of $L$ is added because the displayed limit is false for $L=\varnothing$: its supremum is constantly $-\infty$. Integrability of $Z$ follows from the page's $\mathcal L_p$ setting.
-- source:
--   Delage, Guo & Xu, Shortfall risk models when information of loss function is incomplete, preprint dated April 25, 2018 (later article DOI: https://doi.org/10.1287/opre.2021.2212; numbering follows the preprint), p. 7, (2.12)

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

namespace PrefRobustSR.WorstCase

open MeasureTheory

/-- Equation (2.12), p. 7: the robust gap tends to +∞ as cash tends to -∞. -/
theorem equation_2_12 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (ℝ → ℝ)) (hL : L ⊆ LossClass) (hne : L.Nonempty)
    (Z : Ω → ℝ) (hZ : Integrable Z P) :
    Filter.Tendsto (fun t : ℝ => ⨆ l ∈ L, gap P l Z t)
      Filter.atBot (nhds (⊤ : EReal)) := by sorry

end PrefRobustSR.WorstCase
