-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_comp_div_685ec822924e
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_comp_div_685ec822924e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:31.825343+00:00
-- url     : https://prove2.me/theorems/5e3bfc6b-26e2-411f-94bf-2d922865efad
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform comp div 685ec822924e: P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform comp div 685ec822924e
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform comp div 685ec822924e construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus radial Transform comp div 685ec822924e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L152-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L152-L162

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_comp_div_685ec822924e (e : ℕ) (h : ℝ → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) :
    radialTransform (e + 1) (fun τ => h (τ / ρ ^ 2)) t =
      ρ ^ (2 * (e + 1)) * radialTransform (e + 1) h (t / ρ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«radialTransform_comp_div» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_comp_div_685ec822924e
