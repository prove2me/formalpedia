-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegRadialWeight_gradDens_congr_312b5787b522
-- name    : P2M_GroundTheory_Heights__Heights_RegRadialWeight_gradDens_congr_312b5787b522
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:39.070075+00:00
-- url     : https://prove2.me/theorems/5b31ee08-4010-44f1-8ed3-71e5066f9a5c
-- title:
--   P2 M Ground Theory Heights  Heights Reg Radial Weight grad Dens congr 312b5787b522: P2 M Ground Theory Heights  Heights Reg Radial Weight grad Dens congr 312b5787b522
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Radial Weight grad Dens congr 312b5787b522 construction uses the P2 M Ground Theory Heights  Heights Reg Radial Weight grad Dens congr 312b5787b522 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L35-L39

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

theorem P2M_GroundTheory_Heights__Heights_RegRadialWeight_gradDens_congr_312b5787b522 {m : ℕ} {φ φ' : Fin m → (Fin (m + 1) → ℂ) → ℝ} (v w : (Fin (m + 1) → ℂ) → ℝ)
    {z : Fin (m + 1) → ℂ} (h : ∀ k, hessC (φ k) z = hessC (φ' k) z) :
    gradDens φ v w z = gradDens φ' v w z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegRadialWeight».«gradDens_congr» := P2M_GroundTheory_Heights__Heights_RegRadialWeight_gradDens_congr_312b5787b522
