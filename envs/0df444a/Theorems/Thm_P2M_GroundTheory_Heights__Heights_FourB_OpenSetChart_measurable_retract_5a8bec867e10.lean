-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_measurable_retract_5a8bec867e10
-- name    : P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_measurable_retract_5a8bec867e10
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:08.169403+00:00
-- url     : https://prove2.me/theorems/a3f2f175-346b-5d9b-babd-eba2621ed800
-- title:
--   P2 M Ground Theory Heights  Heights Four B Open Set Chart measurable retract 5a8bec867e10: P2 M Ground Theory Heights  Heights Four B Open Set Chart measurable retract 5a8bec867e10
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Open Set Chart measurable retract 5a8bec867e10 construction uses the P2 M Ground Theory Heights  Heights Four B Open Set Chart measurable retract 5a8bec867e10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OfFubiniStudyCoverMass.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OfFubiniStudyCoverMass.lean#L27-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_HypImp
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OfFubiniStudyCoverMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.FourB.OpenSetChart
variable {D : ℕ} {M : Set (Fin D → ℂ)}

theorem P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_measurable_retract_5a8bec867e10 (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) :
    Measurable (retract x₀ hx₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«OpenSetChart».«measurable_retract» := P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_measurable_retract_5a8bec867e10
