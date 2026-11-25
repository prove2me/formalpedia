-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_coefD_sum_ite__27cc2a00b609
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_coefD_sum_ite__27cc2a00b609
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:14:39.374804+00:00
-- url     : https://prove2.me/theorems/a89daab2-a620-5f76-a7fb-dcbb7bfedd21
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS coef D sum ite  27cc2a00b609: P2 M Reciprocity Theory Chart Restriction DS coef D sum ite  27cc2a00b609
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS coef D sum ite  27cc2a00b609 construction uses the P2 M Reciprocity Theory Chart Restriction DS coef D sum ite  27cc2a00b609 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefDTensActPow.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefDTensActPow.lean#L70-L72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefCExpEntrySummable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
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
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem P2M_ReciprocityTheory_ChartRestriction_DS_coefD_sum_ite__27cc2a00b609 (c : Fin n) (f : Fin n → Fin n → M) :
    ∑ x, ∑ y, (if c = y then f x y else 0) = ∑ x, f x c := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«coefD_sum_ite'» := P2M_ReciprocityTheory_ChartRestriction_DS_coefD_sum_ite__27cc2a00b609
