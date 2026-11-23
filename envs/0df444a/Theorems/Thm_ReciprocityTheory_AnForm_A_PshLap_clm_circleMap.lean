-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_clm_circleMap
-- name    : ReciprocityTheory.AnForm.A.PshLap.clm_circleMap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:08.327131+00:00
-- url     : https://prove2.me/theorems/2ca96bdb-47ed-4ea3-9166-6c93a3a88b4c
-- title:
--   Psh Lap: clm circle Map
-- statement:
--   The Psh Lap construction uses the clm circle Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L24-L26

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

theorem ReciprocityTheory.AnForm.A.PshLap.clm_circleMap (L : ℂ →L[ℝ] ℝ) (r θ : ℝ) :
    L (circleMap 0 r θ) = r * L (circleMap 0 1 θ) := by sorry
