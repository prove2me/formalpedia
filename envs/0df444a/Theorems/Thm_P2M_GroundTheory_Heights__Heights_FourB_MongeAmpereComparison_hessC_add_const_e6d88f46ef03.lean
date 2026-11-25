-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hessC_add_const_e6d88f46ef03
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hessC_add_const_e6d88f46ef03
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:19.439088+00:00
-- url     : https://prove2.me/theorems/8a3e40f3-202d-50aa-899f-56d82f86d1d4
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison hess C add const e6d88f46ef03: P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison hess C add const e6d88f46ef03
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison hess C add const e6d88f46ef03 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison hess C add const e6d88f46ef03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L77-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hessC_add_const_e6d88f46ef03 {D : ℕ} (f : (Fin D → ℂ) → ℝ) (c : ℝ) (z : Fin D → ℂ) :
    hessC (fun y => f y + c) z = hessC f z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereComparison».«hessC_add_const» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hessC_add_const_e6d88f46ef03
