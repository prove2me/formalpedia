-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_USum_diag__apply_d051f1906fda
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_USum_diag__apply_d051f1906fda
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:22.768321+00:00
-- url     : https://prove2.me/theorems/f2be72ae-5a5b-40e6-927c-5cb80313b5fd
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS USum diag  apply d051f1906fda: P2 M Reciprocity Theory Chart Restriction DS USum diag  apply d051f1906fda
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS USum diag  apply d051f1906fda construction uses the P2 M Reciprocity Theory Chart Restriction DS USum diag  apply d051f1906fda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L22-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_InKRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_DiagSubIsKIrrHW
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
variable {n : ℕ} {ε : Fin n → Bool}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_USum_diag__apply_d051f1906fda (φ : V₁ →ₗ[ℂ] V₂) (v : V₁) :
    diagι φ v = ofP ((v : D₁), ((φ v : V₂) : D₂)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«USum».«diagι_apply» := P2M_ReciprocityTheory_ChartRestriction_DS_USum_diag__apply_d051f1906fda
