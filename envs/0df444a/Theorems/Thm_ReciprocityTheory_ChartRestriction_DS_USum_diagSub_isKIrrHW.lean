-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_diagSub_isKIrrHW
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.diagSub_isKIrrHW
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:23.441536+00:00
-- url     : https://prove2.me/theorems/5aaae747-9ef9-4275-8601-2d8e30498f96
-- title:
--   USum: diag Sub is KIrr HW
-- statement:
--   The USum construction uses the diag Sub is KIrr HW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L40-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/DiagSubIsKIrrHW.lean#L40-L99

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

theorem ReciprocityTheory.ChartRestriction.DS.USum.diagSub_isKIrrHW (φ : V₁ →ₗ[ℂ] V₂) {Λ : Fin n → ℝ} (hV₁ : IsKIrrHW ε E₁ Λ V₁)
    (hcomm : ∀ a b (hab : ε a = ε b) (v : V₁),
      E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hV₁.2.1 a b hab _ v.2⟩ : V₂) : D₂)) :
    IsKIrrHW ε (sE E₁ E₂) Λ (diagSub φ) := by sorry
