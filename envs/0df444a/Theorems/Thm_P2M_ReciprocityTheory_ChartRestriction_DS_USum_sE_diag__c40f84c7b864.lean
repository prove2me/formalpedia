-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_USum_sE_diag__c40f84c7b864
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_USum_sE_diag__c40f84c7b864
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:11:52.688595+00:00
-- url     : https://prove2.me/theorems/2795a455-6054-43b7-801d-efeff6414a83
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS USum s E diag  c40f84c7b864: P2 M Reciprocity Theory Chart Restriction DS USum s E diag  c40f84c7b864
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS USum s E diag  c40f84c7b864 construction uses the P2 M Reciprocity Theory Chart Restriction DS USum s E diag  c40f84c7b864 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L31-L38

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_USum_sE_diag__c40f84c7b864 (φ : V₁ →ₗ[ℂ] V₂) (hst : IsKStableSub ε E₁ V₁)
    (hcomm : ∀ a b (hab : ε a = ε b) (v : V₁),
      E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hst a b hab _ v.2⟩ : V₂) : D₂))
    {a b : Fin n} (hab : ε a = ε b) (v : V₁) :
    sE E₁ E₂ a b (diagι φ v) = diagι φ ⟨E₁ a b v, hst a b hab _ v.2⟩ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«USum».«sE_diagι» := P2M_ReciprocityTheory_ChartRestriction_DS_USum_sE_diag__c40f84c7b864
