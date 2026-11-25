-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_USum_isURepOn_s__7ce07fef4a6d
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_USum_isURepOn_s__7ce07fef4a6d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:13.701809+00:00
-- url     : https://prove2.me/theorems/3a330d40-fa62-4b77-a20c-94cc4328c55c
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS USum is URep On s  7ce07fef4a6d: P2 M Reciprocity Theory Chart Restriction DS USum is URep On s  7ce07fef4a6d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS USum is URep On s  7ce07fef4a6d construction uses the P2 M Reciprocity Theory Chart Restriction DS USum is URep On s  7ce07fef4a6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L123-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L123-L135

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix WithLp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
variable {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
variable {ε : Fin n → Bool}
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_USum_isURepOn_s__7ce07fef4a6d {G : Set (Matrix (Fin n) (Fin n) ℂ)} (h₁ : IsURepOn G σ₁) (h₂ : IsURepOn G σ₂) :
    IsURepOn G (sσ σ₁ σ₂) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«USum».«isURepOn_sσ» := P2M_ReciprocityTheory_ChartRestriction_DS_USum_isURepOn_s__7ce07fef4a6d
