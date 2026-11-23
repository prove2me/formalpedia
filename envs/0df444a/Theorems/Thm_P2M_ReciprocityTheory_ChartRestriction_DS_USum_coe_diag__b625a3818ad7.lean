-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_USum_coe_diag__b625a3818ad7
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_USum_coe_diag__b625a3818ad7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:33.527875+00:00
-- url     : https://prove2.me/theorems/4c0412cd-89c3-440e-b9a0-d5678b3f094c
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS USum coe diag  b625a3818ad7: P2 M Reciprocity Theory Chart Restriction DS USum coe diag  b625a3818ad7
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS USum coe diag  b625a3818ad7 construction uses the P2 M Reciprocity Theory Chart Restriction DS USum coe diag  b625a3818ad7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L25-L27

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_USum_coe_diag__b625a3818ad7 (φ : V₁ →ₗ[ℂ] V₂) (v : V₁) :
    ((diagι φ v : sD D₁ D₂) : WithLp 2 (H₁ × H₂)) =
      toLp 2 (((v : D₁) : H₁), (((φ v : V₂) : D₂) : H₂)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«USum».«coe_diagι» := P2M_ReciprocityTheory_ChartRestriction_DS_USum_coe_diag__b625a3818ad7
