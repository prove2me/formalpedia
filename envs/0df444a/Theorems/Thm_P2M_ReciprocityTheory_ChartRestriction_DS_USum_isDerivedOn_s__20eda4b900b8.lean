-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_USum_isDerivedOn_s__20eda4b900b8
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_USum_isDerivedOn_s__20eda4b900b8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:08.790323+00:00
-- url     : https://prove2.me/theorems/595e6188-ab88-4f10-9787-09f30512e959
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS USum is Derived On s  20eda4b900b8: P2 M Reciprocity Theory Chart Restriction DS USum is Derived On s  20eda4b900b8
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS USum is Derived On s  20eda4b900b8 construction uses the P2 M Reciprocity Theory Chart Restriction DS USum is Derived On s  20eda4b900b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L137-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L137-L159

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_USum_isDerivedOn_s__20eda4b900b8 {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
    {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
    (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) :
    IsDerivedOn ε (sσ σ₁ σ₂) (sD D₁ D₂) (sE E₁ E₂) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«USum».«isDerivedOn_sσ» := P2M_ReciprocityTheory_ChartRestriction_DS_USum_isDerivedOn_s__20eda4b900b8
