-- Prove2me | Theorems.Thm_PrefRobustSR_WorstCase_converse_feasible
-- name    : PrefRobustSR.WorstCase.converse_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:32.297017+00:00
-- url     : https://prove2.me/theorems/b2acfe47-0626-4bcd-9b1a-b9e82d448eda
-- title:
--   Proof of Theorem 2.1, p. 7: the worst individual risk is feasible
-- statement:
--   Let $L\subseteq\mathcal L$, let $Z$ be integrable, and suppose that $\hat t=\sup_{l\in L}SR_l^P(Z)$ is a real number. Then
--   $$
--   \sup_{l\in L}\bigl(\mathbb E_P[l(-Z-\hat t)]-l(0)\bigr)\le0,
--   \qquad SR_L^P(Z)\le\hat t.
--   $$
--   The first assertion makes $\hat t$ feasible for the common shortfall constraint; the second is the reverse inequality in (2.9).
--
--   **Formalization Note** The hypothesis that $\hat t$ is real is the finite case considered on the page. The statement does not assume attainment of any individual infimum; the page uses it implicitly. Integrability of $Z$ is implied by its $\mathcal L_p$ assumption.
-- source:
--   Delage, Guo & Xu, Shortfall risk models when information of loss function is incomplete, preprint dated April 25, 2018 (later article DOI: https://doi.org/10.1287/opre.2021.2212; numbering follows the preprint), p. 7, proof of Theorem 2.1, converse display after (2.13)

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

namespace PrefRobustSR.WorstCase

open MeasureTheory

/-- The converse display in the proof of Theorem 2.1, p. 7: when t̂ is real,
it satisfies the robust constraint and bounds the robust optimum. -/
theorem converse_feasible {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (ℝ → ℝ)) (hL : L ⊆ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (th : ℝ)
    (hth : (⨆ l ∈ L, SR P l Z) = (th : EReal)) :
    (⨆ l ∈ L, gap P l Z th) ≤ 0 ∧ SRL P L Z ≤ (th : EReal) := by sorry

end PrefRobustSR.WorstCase
