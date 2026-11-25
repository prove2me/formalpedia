-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_USum_norm_sop
-- name    : ReciprocityTheory.ChartRestriction.DS.USum.norm_sop
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:45:27.914947+00:00
-- url     : https://prove2.me/theorems/c3eeac3f-52b8-4a3d-833b-462e8f398d84
-- title:
--   USum: norm sop
-- statement:
--   The USum construction uses the norm sop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/SopNegComm.lean#L28-L32

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

theorem ReciprocityTheory.ChartRestriction.DS.USum.norm_sop {A : H₁ →L[ℂ] H₁} {B : H₂ →L[ℂ] H₂} (hA : ∀ v, ‖A v‖ = ‖v‖)
    (hB : ∀ v, ‖B v‖ = ‖v‖) (x : WithLp 2 (H₁ × H₂)) : ‖sop A B x‖ = ‖x‖ := by sorry
