-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rm_I_smul_vec
-- name    : ReciprocityTheory.L2DbarEstimates.Y.rm_I_smul_vec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:10.581631+00:00
-- url     : https://prove2.me/theorems/f10cdd2f-3ec3-490c-b2a1-a2c5a3abc2d0
-- title:
--   Y: rm I smul vec
-- statement:
--   The Y construction uses the rm I smul vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L228-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L228-L231

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.Y.rm_I_smul_vec (ξ : Fin n → ℂ) : Complex.I • rmVec ξ = ∑ j, (Complex.I * ξ j) • bas n j := by sorry
