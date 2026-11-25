-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_card_multiLe_succ
-- name    : ReciprocityTheory.L2DbarEstimates.Y.card_multiLe_succ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:31.812272+00:00
-- url     : https://prove2.me/theorems/a59c0db8-ecc2-5b84-bd4f-3215ef29f596
-- title:
--   Y: card multi Le succ
-- statement:
--   The Y construction uses the card multi Le succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IndCount.lean#L25-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/IndCount.lean#L25-L41

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
open Finset

theorem ReciprocityTheory.L2DbarEstimates.Y.card_multiLe_succ (n j : ℕ) :
    (multiLe (n + 1) j).card = ∑ a ∈ range (j + 1), (multiLe n (j - a)).card := by sorry
