-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_lap_nonneg_of_sub_mean
-- name    : ReciprocityTheory.AnForm.A.PshLap.lap_nonneg_of_sub_mean
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:04:53.089875+00:00
-- url     : https://prove2.me/theorems/3c920b49-c097-4a31-8633-68fb11fe1d23
-- title:
--   Psh Lap: lap nonneg of sub mean
-- statement:
--   The Psh Lap construction uses the lap nonneg of sub mean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L344-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L344-L384

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

theorem ReciprocityTheory.AnForm.A.PshLap.lap_nonneg_of_sub_mean (hg : ∀ x ∈ V, HasFDerivAt g (G x) x)
    (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall (0:ℂ) R ⊆ V)
    (hsub : ∀ r ∈ Ioc (0:ℝ) R, g 0 ≤ Real.circleAverage g 0 r) :
    0 ≤ H 0 1 1 + H 0 Complex.I Complex.I := by sorry
