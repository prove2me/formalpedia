-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegRadialWeight_hessC_euclPot_comp_5f9ac46ddec0
-- name    : P2M_GroundTheory_Heights__Heights_RegRadialWeight_hessC_euclPot_comp_5f9ac46ddec0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:44.080512+00:00
-- url     : https://prove2.me/theorems/32a64de1-cd57-4e1a-a5b7-40bd2349a5c4
-- title:
--   P2 M Ground Theory Heights  Heights Reg Radial Weight hess C eucl Pot comp 5f9ac46ddec0: P2 M Ground Theory Heights  Heights Reg Radial Weight hess C eucl Pot comp 5f9ac46ddec0
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Radial Weight hess C eucl Pot comp 5f9ac46ddec0 construction uses the P2 M Ground Theory Heights  Heights Reg Radial Weight hess C eucl Pot comp 5f9ac46ddec0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L60-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L60-L78

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

theorem P2M_GroundTheory_Heights__Heights_RegRadialWeight_hessC_euclPot_comp_5f9ac46ddec0 {D : ℕ} {s : (Fin D → ℂ) → Fin n → ℂ} {y : Fin D → ℂ} (hs : AnalyticAt ℂ s y)
    (x : Fin n → ℂ) : hessC (euclPot ∘ s) y = hessC (fun w => euclPot (s w - x)) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegRadialWeight».«hessC_euclPot_comp» := P2M_GroundTheory_Heights__Heights_RegRadialWeight_hessC_euclPot_comp_5f9ac46ddec0
