-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_actM_sE
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.actM_sE
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:03.824882+00:00
-- url     : https://prove2.me/theorems/3c5685c0-d13d-4c2d-bf41-aa9dff84a6a5
-- title:
--   USum: act M s E
-- statement:
--   The USum construction uses the act M s E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L92-L101

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

theorem ReciprocityTheory.ChartRestriction.DS.USum.actM_sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM (sE E₁ E₂) X = lift (actM E₁ X) (actM E₂ X) := by sorry
