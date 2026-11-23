-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_coefB___casimirK_9818b3c5805b
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_coefB___casimirK_9818b3c5805b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:13.410811+00:00
-- url     : https://prove2.me/theorems/dd5eaa33-a0d3-48b1-9ad1-539aef995492
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS coef B   casimir K 9818b3c5805b: P2 M Reciprocity Theory Chart Restriction DS coef B   casimir K 9818b3c5805b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS coef B   casimir K 9818b3c5805b construction uses the P2 M Reciprocity Theory Chart Restriction DS coef B   casimir K 9818b3c5805b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefBTensSubKStable.lean#L188-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefBTensSubKStable.lean#L188-L194

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefBTensSubKStable
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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_coefB___casimirK_9818b3c5805b (dual : Bool) {S' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hS' : ∀ a b, ∀ v ∈ S', E a b v ∈ S')
    (hι : ∀ a b, ∀ x ∈ S', ι (E a b x) = tensF dual E a b (ι x)) {y : D} (hy : y ∈ S') :
    ι (casimirK ε E y) = casimirK ε (tensF dual E) (ι y) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«coefB_ι_casimirK» := P2M_ReciprocityTheory_ChartRestriction_DS_coefB___casimirK_9818b3c5805b
