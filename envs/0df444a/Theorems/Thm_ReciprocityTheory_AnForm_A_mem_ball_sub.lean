-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mem_ball_sub
-- name    : ReciprocityTheory.AnForm.A.mem_ball_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:14.234921+00:00
-- url     : https://prove2.me/theorems/eb2b8da7-a438-4fba-9315-4c1b15faa13a
-- title:
--   A: mem ball sub
-- statement:
--   The A construction uses the mem ball sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L137-L140

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}

theorem ReciprocityTheory.AnForm.A.mem_ball_sub {ε : ℝ} (hε : 0 < ε) {y : Fin D → ℂ} (hy : ρ.scaled ε y ≠ 0)
    (z : Fin D → ℂ) : z - y ∈ closedBall z ε := by sorry
