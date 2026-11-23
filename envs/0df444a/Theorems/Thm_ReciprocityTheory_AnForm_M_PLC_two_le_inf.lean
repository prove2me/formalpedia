-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_two_le_inf
-- name    : ReciprocityTheory.AnForm.M.PLC.two_le_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:59:07.979804+00:00
-- url     : https://prove2.me/theorems/364e09b2-3bbf-4a90-a18f-a9972907222b
-- title:
--   PLC: two le inf
-- statement:
--   The PLC construction uses the two le inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveB.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveB.lean#L19-L19

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.PLC.two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by sorry
