-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_line_deriv_eventually
-- name    : ReciprocityTheory.AnForm.A.line_deriv_eventually
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:19.57048+00:00
-- url     : https://prove2.me/theorems/58cb9807-5b68-48c1-8f67-1b3f56eb4e52
-- title:
--   A: line deriv eventually
-- statement:
--   The A construction uses the line deriv eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L224-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L224-L234

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ReciprocityTheory.AnForm.A.line_deriv_eventually {φ : E → ℝ} {U : Set E} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    {z : E} (hz : z ∈ U) (w : E) :
    ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => φ (z + s • w)) (fderiv ℝ φ (z + s • w) w) s := by sorry
