-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_factorAd_apply__c08584207034
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_factorAd_apply__c08584207034
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:39.766543+00:00
-- url     : https://prove2.me/theorems/39dca504-13a3-4a33-afe2-66c80426756f
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS factor Ad apply  c08584207034: P2 M Reciprocity Theory Chart Restriction DS factor Ad apply  c08584207034
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS factor Ad apply  c08584207034 construction uses the P2 M Reciprocity Theory Chart Restriction DS factor Ad apply  c08584207034 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L34-L45

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_factorAd_apply__c08584207034 (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) :
    factorAd (M := M) k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«factorAd_apply'» := P2M_ReciprocityTheory_ChartRestriction_DS_factorAd_apply__c08584207034
