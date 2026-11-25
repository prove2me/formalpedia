-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_fderiv2_bound
-- name    : ReciprocityTheory.AnForm.A.regMax_one_fderiv2_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:45.694536+00:00
-- url     : https://prove2.me/theorems/497be6c3-f867-4ee9-9222-1f6189cb2824
-- title:
--   A: reg Max one fderiv2 bound
-- statement:
--   The A construction uses the reg Max one fderiv2 bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L75-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L75-L98

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

theorem ReciprocityTheory.AnForm.A.regMax_one_fderiv2_bound : ∃ C : ℝ, ∀ s : ι → ℝ,
    ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) s‖ ≤ C := by sorry
