-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_coefE___act_9443caaf5a71
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_coefE___act_9443caaf5a71
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:19.926085+00:00
-- url     : https://prove2.me/theorems/8138d71f-e111-58cb-a41e-06cb4fb69763
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS coef E   act 9443caaf5a71: P2 M Reciprocity Theory Chart Restriction DS coef E   act 9443caaf5a71
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS coef E   act 9443caaf5a71 construction uses the P2 M Reciprocity Theory Chart Restriction DS coef E   act 9443caaf5a71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefETensGrpMul.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefETensGrpMul.lean#L69-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefDTensActPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefETensGrpMul
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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_coefE___act_9443caaf5a71 (dual : Bool) {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (X : Matrix (Fin n) (Fin n) ℂ) {v : D} (hv : v ∈ genSub E V') :
    ι (actM E X v) = actM (tensF dual E) X (ι v) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«coefE_ι_act» := P2M_ReciprocityTheory_ChartRestriction_DS_coefE___act_9443caaf5a71
