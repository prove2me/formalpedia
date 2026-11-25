-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_resSeries_coeff_succ__6d30f8d603e9
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_resSeries_coeff_succ__6d30f8d603e9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:13:29.836934+00:00
-- url     : https://prove2.me/theorems/dfd1145a-a8e6-465b-b31f-21a91e4facdc
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS res Series coeff succ  6d30f8d603e9: P2 M Reciprocity Theory Chart Restriction DS res Series coeff succ  6d30f8d603e9
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS res Series coeff succ  6d30f8d603e9 construction uses the P2 M Reciprocity Theory Chart Restriction DS res Series coeff succ  6d30f8d603e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L110-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L110-L116

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_resSeries_coeff_succ__6d30f8d603e9 {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) =
      ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) * a s ^ k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«resSeries_coeff_succ'» := P2M_ReciprocityTheory_ChartRestriction_DS_resSeries_coeff_succ__6d30f8d603e9
