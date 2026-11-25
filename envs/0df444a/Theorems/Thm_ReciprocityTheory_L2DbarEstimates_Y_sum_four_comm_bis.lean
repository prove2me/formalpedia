-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_sum_four_comm_bis
-- name    : ReciprocityTheory.L2DbarEstimates.Y.sum_four_comm_bis
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:01:17.500836+00:00
-- url     : https://prove2.me/theorems/553bce7d-a5a8-4207-80f4-db7d9bcec479
-- title:
--   Y: sum four comm bis
-- statement:
--   The Y construction uses the sum four comm bis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FlatLocA.lean#L67-L74

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.sum_four_comm_bis (T : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ j, ∑ k, T a b j k = ∑ j, ∑ k, ∑ b, ∑ a, T a b j k := by sorry
