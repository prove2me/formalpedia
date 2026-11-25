-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_tsupport_fderiv2_kK
-- name    : ReciprocityTheory.AnForm.A.tsupport_fderiv2_kK
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:17.68396+00:00
-- url     : https://prove2.me/theorems/f093d208-0f09-5616-9dfd-acd971b0075f
-- title:
--   A: tsupport fderiv2 k K
-- statement:
--   The A construction uses the tsupport fderiv2 k K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L50-L54

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

theorem ReciprocityTheory.AnForm.A.tsupport_fderiv2_kK :
    tsupport (fderiv ℝ (fderiv ℝ (kK : (ι → ℝ) → ℝ))) ⊆ closedBall 0 (1 / 2) := by sorry
