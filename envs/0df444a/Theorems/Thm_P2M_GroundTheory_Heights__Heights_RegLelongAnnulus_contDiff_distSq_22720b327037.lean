-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_distSq_22720b327037
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_distSq_22720b327037
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:34.279815+00:00
-- url     : https://prove2.me/theorems/2cff5718-ae33-45df-b23f-529731373688
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff dist Sq 22720b327037: P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff dist Sq 22720b327037
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff dist Sq 22720b327037 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus cont Diff dist Sq 22720b327037 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L331-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L331-L332

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_distSq_22720b327037 : ContDiff ℝ ∞ fun z : Fin n → ℂ => euclPot (z - x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«contDiff_distSq» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_distSq_22720b327037
