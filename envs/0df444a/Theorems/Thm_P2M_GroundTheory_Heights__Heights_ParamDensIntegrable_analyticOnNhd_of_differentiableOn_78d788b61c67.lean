-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ParamDensIntegrable_analyticOnNhd_of_differentiableOn_78d788b61c67
-- name    : P2M_GroundTheory_Heights__Heights_ParamDensIntegrable_analyticOnNhd_of_differentiableOn_78d788b61c67
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:29.886249+00:00
-- url     : https://prove2.me/theorems/67453e57-cf9f-4408-8b5a-289154e13cad
-- title:
--   P2 M Ground Theory Heights  Heights Param Dens Integrable analytic On Nhd of differentiable On 78d788b61c67: P2 M Ground Theory Heights  Heights Param Dens Integrable analytic On Nhd of differentiable
-- statement:
--   The P2 M Ground Theory Heights  Heights Param Dens Integrable analytic On Nhd of differentiable On 78d788b61c67 construction uses the P2 M Ground Theory Heights  Heights Param Dens Integrable analytic On Nhd of differentiable On 78d788b61c67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParamDensIntegrable.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParamDensIntegrable.lean#L14-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParamDensIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ParamDensIntegrable_analyticOnNhd_of_differentiableOn_78d788b61c67 {k m : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ParamDensIntegrable».«analyticOnNhd_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_ParamDensIntegrable_analyticOnNhd_of_differentiableOn_78d788b61c67
