-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_le_circleAverage_of_lap_nonneg
-- name    : ReciprocityTheory.AnForm.A.PshLap.le_circleAverage_of_lap_nonneg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:05:01.911812+00:00
-- url     : https://prove2.me/theorems/124a9706-eb3a-4843-b2de-25b9dc87be64
-- title:
--   Psh Lap: le circle Average of lap nonneg
-- statement:
--   The Psh Lap construction uses the le circle Average of lap nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L273-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L273-L292

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

theorem ReciprocityTheory.AnForm.A.PshLap.le_circleAverage_of_lap_nonneg (hg : ∀ x ∈ V, HasFDerivAt g (G x) x)
    (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : closedBall (0:ℂ) R ⊆ V)
    (hpos : ∀ x ∈ closedBall (0:ℂ) R, ∀ θ : ℝ, 0 ≤ H x (circleMap 0 1 θ) (circleMap 0 1 θ) +
      H x (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I)) :
    g 0 ≤ Real.circleAverage g 0 R := by sorry
