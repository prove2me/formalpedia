-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_angular_period
-- name    : ReciprocityTheory.AnForm.A.PshLap.angular_period
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:57.905056+00:00
-- url     : https://prove2.me/theorems/3cbefc07-8d07-56e5-b6ea-e708dde7a11f
-- title:
--   Psh Lap: angular period
-- statement:
--   The Psh Lap construction uses the angular period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L73-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L73-L110

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

theorem ReciprocityTheory.AnForm.A.PshLap.angular_period (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hGc : ContinuousOn G V)
    (hHc : ContinuousOn H V) {s : ℝ} (hs : closedBall (0:ℂ) |s| ⊆ V) :
    ∫ θ in (0:ℝ)..2*π, G (circleMap 0 s θ) (circleMap 0 1 θ) =
      s * ∫ θ in (0:ℝ)..2*π, H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I)
        (circleMap 0 1 θ * Complex.I) := by sorry
