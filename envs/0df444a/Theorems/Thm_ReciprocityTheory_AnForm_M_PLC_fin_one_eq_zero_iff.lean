-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_fin_one_eq_zero_iff
-- name    : ReciprocityTheory.AnForm.M.PLC.fin_one_eq_zero_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:36.840244+00:00
-- url     : https://prove2.me/theorems/ce177335-58a1-423e-9c8c-3fc5e079ede9
-- title:
--   PLC: fin one eq zero iff
-- statement:
--   The PLC construction uses the fin one eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveB.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveB.lean#L14-L17

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

theorem ReciprocityTheory.AnForm.M.PLC.fin_one_eq_zero_iff (y : Fin 1 → ℂ) : y = 0 ↔ y 0 = 0 := by sorry
