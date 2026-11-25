-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_radialTransform_f4a0f779ce07
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_radialTransform_f4a0f779ce07
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:16:42.277479+00:00
-- url     : https://prove2.me/theorems/2c107581-a933-4a65-898b-f97858fa3ed9
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous radial Transform f4a0f779ce07: P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous radial Transform f4a0f779ce07
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous radial Transform f4a0f779ce07 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous radial Transform f4a0f779ce07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L181-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L181-L185

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_radialTransform_f4a0f779ce07 (e : ℕ) {h : ℝ → ℝ} (hc : Continuous h) :
    Continuous (radialTransform (e + 1) h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«continuous_radialTransform» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_radialTransform_f4a0f779ce07
