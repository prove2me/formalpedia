-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_molli_le_polyMax
-- name    : ReciprocityTheory.AnForm.A.molli_le_polyMax
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:07.396397+00:00
-- url     : https://prove2.me/theorems/ca8305f5-d4c4-47ef-b486-0fba88481193
-- title:
--   A: molli le poly Max
-- statement:
--   The A construction uses the molli le poly Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L187-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMollB.lean#L187-L202

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

theorem ReciprocityTheory.AnForm.A.molli_le_polyMax (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) : molli ρ ε φ z ≤ polyMax φ z ε := by sorry
