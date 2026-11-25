-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_rot_id
-- name    : ReciprocityTheory.AnForm.A.PshLap.rot_id
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:05:06.907406+00:00
-- url     : https://prove2.me/theorems/df63ae5f-1c09-5507-ae8c-94c484e008a4
-- title:
--   Psh Lap: rot id
-- statement:
--   The Psh Lap construction uses the rot id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L150-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L150-L162

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

theorem ReciprocityTheory.AnForm.A.PshLap.rot_id (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (θ : ℝ) :
    B (circleMap 0 1 θ) (circleMap 0 1 θ) +
      B (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I) = B 1 1 + B Complex.I Complex.I := by sorry
