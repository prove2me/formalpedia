-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegRadialWeight_euclPot_nonneg__3fdbce663d88
-- name    : P2M_GroundTheory_Heights__Heights_RegRadialWeight_euclPot_nonneg__3fdbce663d88
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:34.718284+00:00
-- url     : https://prove2.me/theorems/1a34d6f0-129c-4b7a-9cf5-579b50aabcfe
-- title:
--   P2 M Ground Theory Heights  Heights Reg Radial Weight eucl Pot nonneg  3fdbce663d88: P2 M Ground Theory Heights  Heights Reg Radial Weight eucl Pot nonneg  3fdbce663d88
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Radial Weight eucl Pot nonneg  3fdbce663d88 construction uses the P2 M Ground Theory Heights  Heights Reg Radial Weight eucl Pot nonneg  3fdbce663d88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L57-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOnChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRadialPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegRadialWeight
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegRadialWeight
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RegRadialWeight_euclPot_nonneg__3fdbce663d88 (z : Fin n → ℂ) : 0 ≤ euclPot z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegRadialWeight».«euclPot_nonneg'» := P2M_GroundTheory_Heights__Heights_RegRadialWeight_euclPot_nonneg__3fdbce663d88
