-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_continuous_circleMap_uncurry
-- name    : ReciprocityTheory.AnForm.A.PshLap.continuous_circleMap_uncurry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:49.915704+00:00
-- url     : https://prove2.me/theorems/146fd681-80e6-4f70-9c07-02f2823566d3
-- title:
--   Psh Lap: continuous circle Map uncurry
-- statement:
--   The Psh Lap construction uses the continuous circle Map uncurry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L147-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L147-L148

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section

theorem ReciprocityTheory.AnForm.A.PshLap.continuous_circleMap_uncurry : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by sorry
