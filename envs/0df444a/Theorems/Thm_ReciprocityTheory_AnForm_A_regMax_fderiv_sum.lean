-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
-- name    : ReciprocityTheory.AnForm.A.regMax_fderiv_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:14.915801+00:00
-- url     : https://prove2.me/theorems/e7c1e3e0-b8e4-4357-8a88-acf3c185f0d3
-- title:
--   A: reg Max fderiv sum
-- statement:
--   The A construction uses the reg Max fderiv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L18-L30

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
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.regMax_fderiv_sum [DecidableEq ι] {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    ∑ j, fderiv ℝ (regMax (ι := ι) η) t (Pi.single j 1) = 1 := by sorry
