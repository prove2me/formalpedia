-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_log_norm_contDiffOn
-- name    : ReciprocityTheory.AnForm.A.log_norm_contDiffOn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:20:09.742276+00:00
-- url     : https://prove2.me/theorems/d45c2bd4-bfd7-496a-846d-d2cd0bf48c1d
-- title:
--   A: log norm cont Diff On
-- statement:
--   The A construction uses the log norm cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L214-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/HasCompactSupportCompHypInclAt.lean#L214-L225

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HasCompactSupportCompHypInclAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.log_norm_contDiffOn {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {u : (Fin D → ℂ) → ℂ} (hu : DifferentiableOn ℂ u U) (hu0 : ∀ z ∈ U, u z ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => Real.log ‖u z‖) U := by sorry
