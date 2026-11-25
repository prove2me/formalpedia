-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_measurableSet_euclBall_b78b99940d0d
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_measurableSet_euclBall_b78b99940d0d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:39.479237+00:00
-- url     : https://prove2.me/theorems/19dac696-2d32-437d-a2ff-38e4ed6a4279
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus measurable Set eucl Ball b78b99940d0d: P2 M Ground Theory Heights  Heights Reg Lelong Annulus measurable Set eucl Ball b78b99940d0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus measurable Set eucl Ball b78b99940d0d construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus measurable Set eucl Ball b78b99940d0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L341-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L341-L342

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
variable {n : ℕ} (x : Fin n → ℂ)

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_measurableSet_euclBall_b78b99940d0d (ρ : ℝ) : MeasurableSet (euclBall x ρ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«measurableSet_euclBall» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_measurableSet_euclBall_b78b99940d0d
