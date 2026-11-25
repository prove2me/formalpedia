-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_sub_8677133a77df
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_sub_8677133a77df
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:53.609699+00:00
-- url     : https://prove2.me/theorems/6b9ce407-af95-4949-9a16-0973fc16ae41
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform sub 8677133a77df: P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform sub 8677133a77df
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform sub 8677133a77df construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform sub 8677133a77df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L164-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L164-L179

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_sub_8677133a77df (e : ℕ) {f₁ f₂ : ℝ → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (c₁ c₂ t : ℝ) :
    radialTransform (e + 1) (fun τ => c₁ * f₁ τ - c₂ * f₂ τ) t =
      c₁ * radialTransform (e + 1) f₁ t - c₂ * radialTransform (e + 1) f₂ t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«radialTransform_sub» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_sub_8677133a77df
