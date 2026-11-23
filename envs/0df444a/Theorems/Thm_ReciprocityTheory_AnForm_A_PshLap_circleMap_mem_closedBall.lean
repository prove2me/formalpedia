-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleMap_mem_closedBall
-- name    : ReciprocityTheory.AnForm.A.PshLap.circleMap_mem_closedBall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:52.944959+00:00
-- url     : https://prove2.me/theorems/f940dc74-0274-45d4-8a7d-42f4697ff28a
-- title:
--   Psh Lap: circle Map mem closed Ball
-- statement:
--   The Psh Lap construction uses the circle Map mem closed Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L28-L30

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
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}

theorem ReciprocityTheory.AnForm.A.PshLap.circleMap_mem_closedBall {r R θ : ℝ} (h0 : 0 ≤ r) (h : r ≤ R) :
    circleMap 0 r θ ∈ closedBall (0:ℂ) R := by sorry
