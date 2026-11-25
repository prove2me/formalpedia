-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_norm_coordMax_sub_le_half
-- name    : ReciprocityTheory.AnForm.A.norm_coordMax_sub_le_half
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:56.059515+00:00
-- url     : https://prove2.me/theorems/35abfad1-57e8-557d-b1d4-92309461a8cc
-- title:
--   A: norm coord Max sub le half
-- statement:
--   The A construction uses the norm coord Max sub le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L67-L73

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.norm_coordMax_sub_le_half (s₀ s : ι → ℝ) (hs : fderiv ℝ (fderiv ℝ (kK : (ι → ℝ) → ℝ)) s ≠ 0) :
    ‖tmax (s₀ - s) - tmax s₀‖ ≤ 1 / 2 := by sorry
