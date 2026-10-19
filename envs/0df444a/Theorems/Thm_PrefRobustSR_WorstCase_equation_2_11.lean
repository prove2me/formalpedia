-- Prove2me | Theorems.Thm_PrefRobustSR_WorstCase_equation_2_11
-- name    : PrefRobustSR.WorstCase.equation_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:46.730216+00:00
-- url     : https://prove2.me/theorems/cdbd8e1b-64fd-4e56-bee6-addbb9b8105a
-- title:
--   Equation (2.11), p. 7: robust Jensen bound
-- statement:
--   Let $L\subseteq\mathcal L$, let $Z$ be integrable under the probability measure $P$, and let $t\in\mathbb R$. Then
--   $$
--   \sup_{l\in L}\bigl(l(-\mathbb E_P[Z]-t)-l(0)\bigr)
--   \le \sup_{l\in L}\bigl(\mathbb E_P[l(-Z-t)]-l(0)\bigr).
--   $$
--   This is the aggregate Jensen bound used to exclude an unbounded-below robust feasible set.
--
--   **Formalization Note** Integrability of $Z$ replaces the paper's $\mathcal L_p$ hypothesis at this proof step. The supremum is of each whole difference; $l(0)$ depends on $l$.
-- source:
--   Delage, Guo & Xu, Shortfall risk models when information of loss function is incomplete, preprint dated April 25, 2018 (later article DOI: https://doi.org/10.1287/opre.2021.2212; numbering follows the preprint), p. 7, (2.11)

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

namespace PrefRobustSR.WorstCase

open MeasureTheory

/-- Equation (2.11), p. 7: Jensen's bound after taking the supremum over L. -/
theorem equation_2_11 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Set (ℝ → ℝ)) (hL : L ⊆ LossClass)
    (Z : Ω → ℝ) (hZ : Integrable Z P) (t : ℝ) :
    (⨆ l ∈ L, (((l (-(∫ ω, Z ω ∂P) - t) : ℝ) : EReal) -
      ((l 0 : ℝ) : EReal))) ≤
      ⨆ l ∈ L, gap P l Z t := by sorry

end PrefRobustSR.WorstCase
