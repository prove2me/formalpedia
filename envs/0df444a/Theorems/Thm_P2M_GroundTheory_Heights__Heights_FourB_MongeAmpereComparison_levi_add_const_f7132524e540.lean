-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_add_const_f7132524e540
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_add_const_f7132524e540
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:57.605013+00:00
-- url     : https://prove2.me/theorems/e904cd14-9693-5317-9502-7665c4029b47
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison levi add const f7132524e540: P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison levi add const f7132524e540
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison levi add const f7132524e540 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison levi add const f7132524e540 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L49-L52

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

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_add_const_f7132524e540 {ι : Type*} [Fintype ι] (f : (ι → ℂ) → ℝ) (c : ℝ) (z w : ι → ℂ) :
    levi (fun y => f y + c) z w = levi f z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereComparison».«levi_add_const» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_add_const_f7132524e540
