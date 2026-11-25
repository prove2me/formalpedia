-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_mAct_apply__d8d50007d2d3
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_mAct_apply__d8d50007d2d3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:51.462847+00:00
-- url     : https://prove2.me/theorems/f338602d-7be9-4b44-8bd6-4d8bd29c7f6e
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS m Act apply  d8d50007d2d3: P2 M Reciprocity Theory Chart Restriction DS m Act apply  d8d50007d2d3
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS m Act apply  d8d50007d2d3 construction uses the P2 M Reciprocity Theory Chart Restriction DS m Act apply  d8d50007d2d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L31-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_mAct_apply__d8d50007d2d3 (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«mAct_apply'» := P2M_ReciprocityTheory_ChartRestriction_DS_mAct_apply__d8d50007d2d3
