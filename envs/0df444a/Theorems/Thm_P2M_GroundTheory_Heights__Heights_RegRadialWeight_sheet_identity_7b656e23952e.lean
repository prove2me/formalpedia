-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegRadialWeight_sheet_identity_7b656e23952e
-- name    : P2M_GroundTheory_Heights__Heights_RegRadialWeight_sheet_identity_7b656e23952e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:08.631144+00:00
-- url     : https://prove2.me/theorems/f75ad905-03e9-4ef8-929f-1a3a433b46c0
-- title:
--   P2 M Ground Theory Heights  Heights Reg Radial Weight sheet identity 7b656e23952e: P2 M Ground Theory Heights  Heights Reg Radial Weight sheet identity 7b656e23952e
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Radial Weight sheet identity 7b656e23952e construction uses the P2 M Ground Theory Heights  Heights Reg Radial Weight sheet identity 7b656e23952e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L95-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L95-L164

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

theorem P2M_GroundTheory_Heights__Heights_RegRadialWeight_sheet_identity_7b656e23952e (hLP : MaDensLogPow.Statement) {e : ℕ} {s : (Fin (e + 1 + 1) → ℂ) → Fin n → ℂ}
    {y : Fin (e + 1 + 1) → ℂ} (hs : AnalyticAt ℂ s y) (x : Fin n → ℂ) (G : (Fin n → ℂ) → ℝ) (Q a b : ℝ → ℝ)
    (hQ : ContDiff ℝ 2 Q) (hQ0 : deriv Q 0 = a 0) (hQ0' : deriv (deriv Q) 0 = 0) (hb0 : b 0 = 0)
    (hQt : ∀ t, 0 < t → deriv Q t * t ^ (e + 1) = a t * t ^ (e + 1) - b t ∧
      deriv (deriv Q) t * t ^ (e + 2) = ((e + 1 : ℕ) : ℝ) * b t) :
    b (euclPot (s y - x)) * maDens (fun k => vecCons G (fun _ : Fin (e + 1) => logDistSq x) k ∘ s) y =
      a (euclPot (s y - x)) * maDens (fun k => vecCons G (fun _ : Fin (e + 1) => euclPot) k ∘ s) y -
        1 * maDens (fun k => vecCons (fun z => Q (euclPot (z - x))) (vecCons G fun _ : Fin e => euclPot) k ∘ s) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegRadialWeight».«sheet_identity» := P2M_GroundTheory_Heights__Heights_RegRadialWeight_sheet_identity_7b656e23952e
