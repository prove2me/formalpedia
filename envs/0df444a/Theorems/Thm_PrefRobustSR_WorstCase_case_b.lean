-- Prove2me | Theorems.Thm_PrefRobustSR_WorstCase_case_b
-- name    : PrefRobustSR.WorstCase.case_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:30.778155+00:00
-- url     : https://prove2.me/theorems/b42d1cce-5ae3-4048-94a9-63743d3de165
-- title:
--   Proof of Theorem 2.1, p. 7: the empty feasible-set case
-- statement:
--   Let $L\subseteq\mathcal L$ and let $Z$ be integrable under $P$. If there is no real cash amount satisfying the common shortfall constraint, then both sides of (2.9) are infinite:
--   $$
--   SR_L^P(Z)=+\infty,\qquad \sup_{l\in L}SR_l^P(Z)=+\infty.
--   $$
--   This is case (b) in the paper's proof and completes the infinite-value branch of the representation.
--
--   **Formalization Note** Integrability of $Z$ is implied by $Z\in\mathcal L_p$ in the paper. The values and the empty-set infimum are interpreted in the extended reals.
-- source:
--   Delage, Guo & Xu, Shortfall risk models when information of loss function is incomplete, preprint dated April 25, 2018 (later article DOI: https://doi.org/10.1287/opre.2021.2212; numbering follows the preprint), p. 7, proof of Theorem 2.1, case (b)

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

namespace PrefRobustSR.WorstCase

open MeasureTheory

/-- Case (b) in the proof of Theorem 2.1, p. 7: if no common cash
amount is feasible, both sides of (2.9) are +∞. -/
theorem case_b {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (ℝ → ℝ)) (hL : L ⊆ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P)
    (h : ¬ ∃ t : ℝ, (⨆ l ∈ L, gap P l Z t) ≤ 0) :
    SRL P L Z = ⊤ ∧ (⨆ l ∈ L, SR P l Z) = ⊤ := by sorry

end PrefRobustSR.WorstCase
