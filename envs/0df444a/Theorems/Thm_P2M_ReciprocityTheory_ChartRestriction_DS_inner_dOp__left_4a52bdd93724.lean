-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_inner_dOp__left_4a52bdd93724
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_inner_dOp__left_4a52bdd93724
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:53.081801+00:00
-- url     : https://prove2.me/theorems/23822258-1881-5bf2-b814-e932ee150c41
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS inner d Op  left 4a52bdd93724: P2 M Reciprocity Theory Chart Restriction DS inner d Op  left 4a52bdd93724
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS inner d Op  left 4a52bdd93724 construction uses the P2 M Reciprocity Theory Chart Restriction DS inner d Op  left 4a52bdd93724 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L151-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean#L151-L166

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
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
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem P2M_ReciprocityTheory_ChartRestriction_DS_inner_dOp__left_4a52bdd93724 {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W}
    (hU : IsInfUnitary ε E) (hEC : CommutesCAR E cp cm)
    (hadj : ∀ (i a : Fin n) (x y : W), inner ℂ (cp i a x) y = inner ℂ x (cm i a y)) (x y : W) :
    inner ℂ (dOp' ε E cm x) y = inner ℂ x (dOp ε E cp y) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«inner_dOp'_left» := P2M_ReciprocityTheory_ChartRestriction_DS_inner_dOp__left_4a52bdd93724
