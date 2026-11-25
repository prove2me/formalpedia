-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_nsq_nonneg__b8329bf5ba4b
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_nsq_nonneg__b8329bf5ba4b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:13:22.769398+00:00
-- url     : https://prove2.me/theorems/a43e70c1-c215-4d74-b719-d204ff83ac19
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS nsq nonneg  b8329bf5ba4b: P2 M Reciprocity Theory Chart Restriction DS nsq nonneg  b8329bf5ba4b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS nsq nonneg  b8329bf5ba4b construction uses the P2 M Reciprocity Theory Chart Restriction DS nsq nonneg  b8329bf5ba4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L23-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_nsq_nonneg__b8329bf5ba4b (x : Fin n → ℝ) : 0 ≤ nsq x := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«nsq_nonneg'» := P2M_ReciprocityTheory_ChartRestriction_DS_nsq_nonneg__b8329bf5ba4b
