-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_nonneg_983e714bd225
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_nonneg_983e714bd225
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:21.329598+00:00
-- url     : https://prove2.me/theorems/cf045fbd-0234-4ee6-8d3a-742b36c94948
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus dist Sq nonneg 983e714bd225: P2 M Ground Theory Heights  Heights Reg Lelong Annulus dist Sq nonneg 983e714bd225
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus dist Sq nonneg 983e714bd225 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus dist Sq nonneg 983e714bd225 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L334-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L334-L335

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_nonneg_983e714bd225 (z : Fin n → ℂ) : 0 ≤ euclPot (z - x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«distSq_nonneg» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_nonneg_983e714bd225
