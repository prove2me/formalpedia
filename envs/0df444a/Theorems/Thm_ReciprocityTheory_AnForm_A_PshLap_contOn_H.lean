-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_contOn_H
-- name    : ReciprocityTheory.AnForm.A.PshLap.contOn_H
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:04:58.12383+00:00
-- url     : https://prove2.me/theorems/43984b6a-1dc6-4e4e-9db0-1f1669792057
-- title:
--   Psh Lap: cont On H
-- statement:
--   The Psh Lap construction uses the cont On H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L261-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L261-L271

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

theorem ReciprocityTheory.AnForm.A.PshLap.contOn_H (hHc : ContinuousOn H V) {R a : ℝ} (hR : closedBall (0:ℂ) R ⊆ V) :
    ContinuousOn (Function.uncurry fun s θ =>
      H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
        H (circleMap 0 s θ) (circleMap 0 1 θ * Complex.I) (circleMap 0 1 θ * Complex.I))
      (Icc 0 R ×ˢ Icc 0 a) := by sorry
