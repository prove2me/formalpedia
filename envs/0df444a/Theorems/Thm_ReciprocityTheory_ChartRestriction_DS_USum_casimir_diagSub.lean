-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_casimir_diagSub
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.casimir_diagSub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:47.305772+00:00
-- url     : https://prove2.me/theorems/cd530488-455b-40d4-b240-489e8b2e0c7e
-- title:
--   USum: casimir diag Sub
-- statement:
--   The USum construction uses the casimir diag Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L101-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L101-L108

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

theorem ReciprocityTheory.ChartRestriction.DS.USum.casimir_diagSub (φ : V₁ →ₗ[ℂ] V₂) {c : ℂ}
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = c • v) (hc₂ : ∀ v ∈ V₂, casimir E₂ v = c • v) :
    ∀ x ∈ diagSub φ, casimir (sE E₁ E₂) x = c • x := by sorry
