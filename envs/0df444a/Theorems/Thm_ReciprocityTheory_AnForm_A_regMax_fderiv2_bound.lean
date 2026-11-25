-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv2_bound
-- name    : ReciprocityTheory.AnForm.A.regMax_fderiv2_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:40.579644+00:00
-- url     : https://prove2.me/theorems/2165431e-11ff-42b2-82d5-081d2aaa7716
-- title:
--   A: reg Max fderiv2 bound
-- statement:
--   The A construction uses the reg Max fderiv2 bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L123-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L123-L135

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

theorem ReciprocityTheory.AnForm.A.regMax_fderiv2_bound : ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ (t v w : ι → ℝ), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
    |fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t v w| ≤ C / η := by sorry
