-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mul_coord_bounds
-- name    : ReciprocityTheory.AnForm.A.mul_coord_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:45.559775+00:00
-- url     : https://prove2.me/theorems/44c2d089-e54a-40f1-a1d7-fd928dad835a
-- title:
--   A: mul coord bounds
-- statement:
--   The A construction uses the mul coord bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L166-L171

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
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
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.mul_coord_bounds {η : ℝ} (hη : 0 ≤ η) {h : ι → ℝ} (hh : kK h ≠ 0) (j : ι) :
    -(η / 2) ≤ η * h j ∧ η * h j ≤ η / 2 := by sorry
