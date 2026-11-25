-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hasDerivAt_cutoff_d9e21ca0833b
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hasDerivAt_cutoff_d9e21ca0833b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:46.165301+00:00
-- url     : https://prove2.me/theorems/2a08c3fb-debd-5af8-af55-e308a9ec419e
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison has Deriv At cutoff d9e21ca0833b: P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison has Deriv At cutoff d9e21ca0833b
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison has Deriv At cutoff d9e21ca0833b construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison has Deriv At cutoff d9e21ca0833b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L20-L21

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

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hasDerivAt_cutoff_d9e21ca0833b (t : ℝ) : HasDerivAt cutoff (Real.smoothTransition t) t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereComparison».«hasDerivAt_cutoff» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hasDerivAt_cutoff_d9e21ca0833b
