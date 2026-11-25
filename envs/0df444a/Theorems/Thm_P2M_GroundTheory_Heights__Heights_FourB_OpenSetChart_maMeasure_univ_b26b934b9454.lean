-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_maMeasure_univ_b26b934b9454
-- name    : P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_maMeasure_univ_b26b934b9454
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:12.28581+00:00
-- url     : https://prove2.me/theorems/992ff7ab-5ffd-4661-8658-1d61a5e5dd06
-- title:
--   P2 M Ground Theory Heights  Heights Four B Open Set Chart ma Measure univ b26b934b9454: P2 M Ground Theory Heights  Heights Four B Open Set Chart ma Measure univ b26b934b9454
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Open Set Chart ma Measure univ b26b934b9454 construction uses the P2 M Ground Theory Heights  Heights Four B Open Set Chart ma Measure univ b26b934b9454 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OfFubiniStudyCoverMass.lean#L71-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OfFubiniStudyCoverMass.lean#L71-L88

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

theorem P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_maMeasure_univ_b26b934b9454 (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (u : M → ℝ) :
    maMeasure (atlas hM x₀ hx₀) (fun _ => LocPot.ofFun u) Set.univ =
      ∫⁻ y in M, ENNReal.ofReal (maDens (fun _ y' => u (retract x₀ hx₀ y')) y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«OpenSetChart».«maMeasure_univ» := P2M_GroundTheory_Heights__Heights_FourB_OpenSetChart_maMeasure_univ_b26b934b9454
