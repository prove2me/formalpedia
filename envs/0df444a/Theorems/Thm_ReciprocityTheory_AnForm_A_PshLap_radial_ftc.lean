-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_radial_ftc
-- name    : ReciprocityTheory.AnForm.A.PshLap.radial_ftc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:05:13.811438+00:00
-- url     : https://prove2.me/theorems/879f2c94-33d4-42b5-ae99-7c274ca9ff3d
-- title:
--   Psh Lap: radial ftc
-- statement:
--   The Psh Lap construction uses the radial ftc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L32-L44

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

theorem ReciprocityTheory.AnForm.A.PshLap.radial_ftc (hg : ∀ x ∈ V, HasFDerivAt g (G x) x) (hGc : ContinuousOn G V)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : closedBall (0:ℂ) R ⊆ V) (θ : ℝ) :
    g (circleMap 0 R θ) - g 0 = ∫ r in (0:ℝ)..R, G (circleMap 0 r θ) (circleMap 0 1 θ) := by sorry
