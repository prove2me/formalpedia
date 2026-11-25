-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleAverage_sub_le
-- name    : ReciprocityTheory.AnForm.A.PshLap.circleAverage_sub_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:59.877603+00:00
-- url     : https://prove2.me/theorems/1dd93248-fef6-5a29-93b7-8f2a3b5eb163
-- title:
--   Psh Lap: circle Average sub le
-- statement:
--   The Psh Lap construction uses the circle Average sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L294-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L294-L342

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
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}

theorem ReciprocityTheory.AnForm.A.PshLap.circleAverage_sub_le (hg : ∀ x ∈ V, HasFDerivAt g (G x) x)
    (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : closedBall (0:ℂ) R ⊆ V) (K : ℝ)
    (hK : ∀ x ∈ closedBall (0:ℂ) R, ∀ θ : ℝ, H x (circleMap 0 1 θ) (circleMap 0 1 θ) +
      H x (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I) ≤ K) :
    Real.circleAverage g 0 R - g 0 ≤ K * R ^ 2 / 4 := by sorry
