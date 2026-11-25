-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_logDistSmooth_eventuallyEq_9826a6050e70
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_logDistSmooth_eventuallyEq_9826a6050e70
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:16:53.971984+00:00
-- url     : https://prove2.me/theorems/59d033b5-690a-4be7-8a39-02949acf6c17
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus log Dist Smooth eventually Eq 9826a6050e70: P2 M Ground Theory Heights  Heights Reg Lelong Annulus log Dist Smooth eventually Eq 9826a6050e70
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus log Dist Smooth eventually Eq 9826a6050e70 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus log Dist Smooth eventually Eq 9826a6050e70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L411-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L411-L420

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_logDistSmooth_eventuallyEq_9826a6050e70 {r : ℝ} (hr : 0 < r) {z : Fin n → ℂ} (hz : r ^ 2 / 4 < euclPot (z - x)) :
    logDistSmooth x hr =ᶠ[𝓝 z] logDistSq x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«logDistSmooth_eventuallyEq» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_logDistSmooth_eventuallyEq_9826a6050e70
