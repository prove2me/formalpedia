-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_molli_submean
-- name    : ReciprocityTheory.AnForm.A.molli_submean
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:37.083808+00:00
-- url     : https://prove2.me/theorems/ce4c322f-ae6d-4907-a967-943dee0ae803
-- title:
--   A: molli submean
-- statement:
--   The A construction uses the molli submean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L218-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L218-L267

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

theorem ReciprocityTheory.AnForm.A.molli_submean (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z w : Fin D → ℂ} (hd : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ shrink U ε) :
    molli ρ ε φ z ≤ circleAverage (fun ζ : ℂ => molli ρ ε φ (z + ζ • w)) 0 1 := by sorry
