-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_coefE___pow_8e1cd4cc143f
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_coefE___pow_8e1cd4cc143f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:25.808423+00:00
-- url     : https://prove2.me/theorems/184a16ce-2ccb-58f5-952b-46804bc59e8a
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS coef E   pow 8e1cd4cc143f: P2 M Reciprocity Theory Chart Restriction DS coef E   pow 8e1cd4cc143f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS coef E   pow 8e1cd4cc143f construction uses the P2 M Reciprocity Theory Chart Restriction DS coef E   pow 8e1cd4cc143f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefETensGrpMul.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefETensGrpMul.lean#L92-L101

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_coefE___pow_8e1cd4cc143f (dual : Bool) {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) {y : D} (hy : y ∈ genSub E V') :
    ι (((actM E X) ^ m) y) = ((actM (tensF dual E) X) ^ m) (ι y) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«coefE_ι_pow» := P2M_ReciprocityTheory_ChartRestriction_DS_coefE___pow_8e1cd4cc143f
