-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_succ_le_inf
-- name    : ReciprocityTheory.AnForm.A.succ_le_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:01.083903+00:00
-- url     : https://prove2.me/theorems/bcdbdb3c-e18a-4a1f-a1ec-4350c2bc6fef
-- title:
--   A: succ le inf
-- statement:
--   The A construction uses the succ le inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L13-L13

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

theorem ReciprocityTheory.AnForm.A.succ_le_inf (m : ℕ) : (m : WithTop ℕ∞) + 1 ≤ ∞ := by sorry
