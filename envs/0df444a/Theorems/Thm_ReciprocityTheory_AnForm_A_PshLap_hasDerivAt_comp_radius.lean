-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_hasDerivAt_comp_radius
-- name    : ReciprocityTheory.AnForm.A.PshLap.hasDerivAt_comp_radius
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:04:49.634197+00:00
-- url     : https://prove2.me/theorems/2d7aeaae-e485-5a16-9121-85a8e0957061
-- title:
--   Psh Lap: has Deriv At comp radius
-- statement:
--   The Psh Lap construction uses the has Deriv At comp radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L16-L19

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

theorem ReciprocityTheory.AnForm.A.PshLap.hasDerivAt_comp_radius {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℂ → F} {φ' : ℂ →L[ℝ] F} (r θ : ℝ) (h : HasFDerivAt φ φ' (circleMap 0 r θ)) :
    HasDerivAt (fun s : ℝ => φ (circleMap 0 s θ)) (φ' (circleMap 0 1 θ)) r := by sorry
