-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hasDerivAt_line_fderiv
-- name    : ReciprocityTheory.AnForm.A.hasDerivAt_line_fderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:02.055256+00:00
-- url     : https://prove2.me/theorems/7f5f475b-747e-4f81-b434-eccbd7ee0473
-- title:
--   A: has Deriv At line fderiv
-- statement:
--   The A construction uses the has Deriv At line fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L214-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L214-L222

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

theorem ReciprocityTheory.AnForm.A.hasDerivAt_line_fderiv {φ : E → ℝ} {U : Set E} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    {z : E} (hz : z ∈ U) (w : E) :
    HasDerivAt (fun s : ℝ => fderiv ℝ φ (z + s • w) w) (fderiv ℝ (fderiv ℝ φ) z w w) 0 := by sorry
