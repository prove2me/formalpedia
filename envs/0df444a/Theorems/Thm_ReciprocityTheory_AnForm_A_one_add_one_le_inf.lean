-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_one_add_one_le_inf
-- name    : ReciprocityTheory.AnForm.A.one_add_one_le_inf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:05.334665+00:00
-- url     : https://prove2.me/theorems/3c100078-69b7-42d3-8d58-7e1389d99f2d
-- title:
--   A: one add one le inf
-- statement:
--   The A construction uses the one add one le inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L14-L14

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

theorem ReciprocityTheory.AnForm.A.one_add_one_le_inf : (1 : WithTop ℕ∞) + 1 ≤ ∞ := by sorry
