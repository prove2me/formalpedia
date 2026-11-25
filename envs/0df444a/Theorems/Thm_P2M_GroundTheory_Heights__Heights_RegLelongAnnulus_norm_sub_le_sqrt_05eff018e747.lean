-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_norm_sub_le_sqrt_05eff018e747
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_norm_sub_le_sqrt_05eff018e747
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:45.524905+00:00
-- url     : https://prove2.me/theorems/3529e639-1732-4b7e-9582-d06007d6eb2e
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus norm sub le sqrt 05eff018e747: P2 M Ground Theory Heights  Heights Reg Lelong Annulus norm sub le sqrt 05eff018e747
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus norm sub le sqrt 05eff018e747 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus norm sub le sqrt 05eff018e747 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L344-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L344-L349

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_norm_sub_le_sqrt_05eff018e747 (z : Fin n → ℂ) : ‖z - x‖ ≤ Real.sqrt (euclPot (z - x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«norm_sub_le_sqrt» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_norm_sub_le_sqrt_05eff018e747
