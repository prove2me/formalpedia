-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_add_pos_20ae4db78bb9
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_add_pos_20ae4db78bb9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:16:22.503802+00:00
-- url     : https://prove2.me/theorems/ad08f484-2c3f-5593-b12e-edff56f9d5b0
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus dist Sq add pos 20ae4db78bb9: P2 M Ground Theory Heights  Heights Reg Lelong Annulus dist Sq add pos 20ae4db78bb9
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus dist Sq add pos 20ae4db78bb9 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus dist Sq add pos 20ae4db78bb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L392-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L392-L405

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_add_pos_20ae4db78bb9 {r : ℝ} (hr : 0 < r) (z : Fin n → ℂ) :
    0 < euclPot (z - x) + r ^ 2 * smallBump hr (euclPot (z - x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«distSq_add_pos» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_add_pos_20ae4db78bb9
