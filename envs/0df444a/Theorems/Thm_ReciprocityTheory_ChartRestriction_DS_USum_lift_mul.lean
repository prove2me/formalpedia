-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_lift_mul
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.lift_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:37.071991+00:00
-- url     : https://prove2.me/theorems/f7d56273-bc0e-4cd2-86e6-183c207a5b48
-- title:
--   USum: lift mul
-- statement:
--   The USum construction uses the lift mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L72-L73

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

theorem ReciprocityTheory.ChartRestriction.DS.USum.lift_mul (F₁ G₁ : Module.End ℂ D₁) (F₂ G₂ : Module.End ℂ D₂) :
    lift (F₁ * G₁) (F₂ * G₂) = lift F₁ F₂ * lift G₁ G₂ := by sorry
