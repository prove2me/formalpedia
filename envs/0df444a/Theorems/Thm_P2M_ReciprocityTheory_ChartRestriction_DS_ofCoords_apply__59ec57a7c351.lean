-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_ofCoords_apply__59ec57a7c351
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_ofCoords_apply__59ec57a7c351
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:13:14.133003+00:00
-- url     : https://prove2.me/theorems/4446d265-b227-4b20-ad11-7b2e4cd03a5f
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS of Coords apply  59ec57a7c351: P2 M Reciprocity Theory Chart Restriction DS of Coords apply  59ec57a7c351
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS of Coords apply  59ec57a7c351 construction uses the P2 M Reciprocity Theory Chart Restriction DS of Coords apply  59ec57a7c351 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/PositionPrependMemNoncompactPositionSubmodule.lean#L20-L22

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_ofCoords_apply__59ec57a7c351 {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    ofCoords k f x κ = f κ x := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«ofCoords_apply'» := P2M_ReciprocityTheory_ChartRestriction_DS_ofCoords_apply__59ec57a7c351
