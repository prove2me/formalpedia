-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegRadialWeight_maDens_swap_79fd7ac86743
-- name    : P2M_GroundTheory_Heights__Heights_RegRadialWeight_maDens_swap_79fd7ac86743
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:20:06.796456+00:00
-- url     : https://prove2.me/theorems/04661717-3681-424d-9f36-3d02e87eb5b2
-- title:
--   P2 M Ground Theory Heights  Heights Reg Radial Weight ma Dens swap 79fd7ac86743: P2 M Ground Theory Heights  Heights Reg Radial Weight ma Dens swap 79fd7ac86743
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Radial Weight ma Dens swap 79fd7ac86743 construction uses the P2 M Ground Theory Heights  Heights Reg Radial Weight ma Dens swap 79fd7ac86743 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L41-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L41-L55

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

theorem P2M_GroundTheory_Heights__Heights_RegRadialWeight_maDens_swap_79fd7ac86743 {e : ℕ} (X G : (Fin (e + 1 + 1) → ℂ) → ℝ) (z : Fin (e + 1 + 1) → ℂ) :
    maDens (Fin.cons X (Fin.cons G fun _ : Fin e => X)) z = maDens (Fin.cons G fun _ : Fin (e + 1) => X) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegRadialWeight».«maDens_swap» := P2M_GroundTheory_Heights__Heights_RegRadialWeight_maDens_swap_79fd7ac86743
