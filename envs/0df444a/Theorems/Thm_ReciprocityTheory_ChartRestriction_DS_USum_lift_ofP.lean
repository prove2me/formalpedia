-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_lift_ofP
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.lift_ofP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:36.412198+00:00
-- url     : https://prove2.me/theorems/61c6ec92-ceff-4cf2-9721-56ed63fd0f48
-- title:
--   USum: lift of P
-- statement:
--   The USum construction uses the lift of P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L69-L70

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

theorem ReciprocityTheory.ChartRestriction.DS.USum.lift_ofP (F₁ : Module.End ℂ D₁) (F₂ : Module.End ℂ D₂) (p : D₁ × D₂) :
    lift F₁ F₂ (ofP p) = ofP (F₁ p.1, F₂ p.2) := by sorry
