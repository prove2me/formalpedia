-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_hasDerivAt_circleMap_radius
-- name    : ReciprocityTheory.AnForm.A.PshLap.hasDerivAt_circleMap_radius
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:35.129151+00:00
-- url     : https://prove2.me/theorems/2f3d418d-1f25-4d88-9db9-d8daadae90a9
-- title:
--   Psh Lap: has Deriv At circle Map radius
-- statement:
--   The Psh Lap construction uses the has Deriv At circle Map radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L11-L14

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

theorem ReciprocityTheory.AnForm.A.PshLap.hasDerivAt_circleMap_radius (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => circleMap 0 s θ) (circleMap 0 1 θ) r := by sorry
