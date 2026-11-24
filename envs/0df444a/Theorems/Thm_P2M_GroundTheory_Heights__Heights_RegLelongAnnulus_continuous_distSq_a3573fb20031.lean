-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_distSq_a3573fb20031
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_distSq_a3573fb20031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:41.155496+00:00
-- url     : https://prove2.me/theorems/c51bdad1-d55b-4756-b566-b91041ac74ad
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous dist Sq a3573fb20031: P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous dist Sq a3573fb20031
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous dist Sq a3573fb20031 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus continuous dist Sq a3573fb20031 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L328-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L328-L329

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_distSq_a3573fb20031 : Continuous fun z : Fin n → ℂ => euclPot (z - x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«continuous_distSq» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_distSq_a3573fb20031
