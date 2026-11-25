-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_eq_norm__fa929b459380
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_eq_norm__fa929b459380
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:51.872107+00:00
-- url     : https://prove2.me/theorems/24af7b29-5a94-4226-85ef-68343e36b1d0
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS sqrt nsq eq norm  fa929b459380: P2 M Reciprocity Theory Chart Restriction DS sqrt nsq eq norm  fa929b459380
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS sqrt nsq eq norm  fa929b459380 construction uses the P2 M Reciprocity Theory Chart Restriction DS sqrt nsq eq norm  fa929b459380 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/WeightBound.lean#L13-L21

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_eq_norm__fa929b459380 (x : Fin n → ℝ) :
    √(nsq x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«sqrt_nsq_eq_norm'» := P2M_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_eq_norm__fa929b459380
