-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_mapsTo_rect
-- name    : ReciprocityTheory.AnForm.A.PshLap.mapsTo_rect
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:42.876287+00:00
-- url     : https://prove2.me/theorems/a8fe431d-0050-453c-be2e-e75d67e646af
-- title:
--   Psh Lap: maps To rect
-- statement:
--   The Psh Lap construction uses the maps To rect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L173-L175

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
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}

theorem ReciprocityTheory.AnForm.A.PshLap.mapsTo_rect {R a : ℝ} (hR : closedBall (0:ℂ) R ⊆ V) :
    MapsTo (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) (Icc 0 R ×ˢ Icc 0 a) V := by sorry
