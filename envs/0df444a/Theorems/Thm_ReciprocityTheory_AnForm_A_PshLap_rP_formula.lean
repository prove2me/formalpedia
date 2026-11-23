-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_rP_formula
-- name    : ReciprocityTheory.AnForm.A.PshLap.rP_formula
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:08.044109+00:00
-- url     : https://prove2.me/theorems/346ff7af-ab09-4592-bf0f-22351755ee73
-- title:
--   Psh Lap: r P formula
-- statement:
--   The Psh Lap construction uses the r P formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L204-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshLap.lean#L204-L247

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

theorem ReciprocityTheory.AnForm.A.PshLap.rP_formula (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hGc : ContinuousOn G V)
    (hHc : ContinuousOn H V) {R r : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R)
    (hR : closedBall (0:ℂ) R ⊆ V) :
    r * Pr G r = ∫ s in (0:ℝ)..r, s * Lap H s := by sorry
