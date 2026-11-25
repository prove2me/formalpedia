-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_nonneg
-- name    : ReciprocityTheory.AnForm.A.regMax_fderiv_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:05.335237+00:00
-- url     : https://prove2.me/theorems/5b77c3c5-ad46-4b9b-b1b6-ea1c695ccb93
-- title:
--   A: reg Max fderiv nonneg
-- statement:
--   The A construction uses the reg Max fderiv nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L278-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L278-L289

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
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.regMax_fderiv_nonneg {η : ℝ} (hη : 0 < η) (p e : ι → ℝ) (he : 0 ≤ e) :
    0 ≤ fderiv ℝ (regMax (ι := ι) η) p e := by sorry
