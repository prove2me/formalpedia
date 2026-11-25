-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_annWeight_le_408cf7b69dc2
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_annWeight_le_408cf7b69dc2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:27.291077+00:00
-- url     : https://prove2.me/theorems/b591078c-bc43-4773-a337-c462ca710d0f
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs ann Weight le 408cf7b69dc2: P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs ann Weight le 408cf7b69dc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs ann Weight le 408cf7b69dc2 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs ann Weight le 408cf7b69dc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L468-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L468-L473

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
variable {r s : ℝ} (e : ℕ)

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_annWeight_le_408cf7b69dc2 (hr : 0 < r) (hs : 0 < s) (k : ℕ) (t : ℝ) :
    |annWeight r s e k t| ≤ r ^ (2 * (e + 1)) + s ^ (2 * (e + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«abs_annWeight_le» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_annWeight_le_408cf7b69dc2
