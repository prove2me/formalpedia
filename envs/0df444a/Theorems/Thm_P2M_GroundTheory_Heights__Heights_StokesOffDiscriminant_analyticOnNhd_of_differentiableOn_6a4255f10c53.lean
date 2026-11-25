-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_analyticOnNhd_of_differentiableOn_6a4255f10c53
-- name    : P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_analyticOnNhd_of_differentiableOn_6a4255f10c53
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:49:07.220518+00:00
-- url     : https://prove2.me/theorems/2b2da8b1-9908-50e8-8cab-c99baa1bcf7c
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Off Discriminant analytic On Nhd of differentiable On 6a4255f10c53: P2 M Ground Theory Heights  Heights Stokes Off Discriminant analytic On Nhd of differenti
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Off Discriminant analytic On Nhd of differentiable On 6a4255f10c53 construction uses the P2 M Ground Theory Heights  Heights Stokes Off Discriminant analytic On Nhd of differentiable On 6a4255f10c53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L190-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StokesOffDiscriminantWindow.lean#L190-L193

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StStokesOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StokesOffDiscriminantWindow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_d56f1b066651

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
open GroundTheory.Heights₂.Heights.StokesOffDiscriminant
variable {n D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_analyticOnNhd_of_differentiableOn_6a4255f10c53 {s : (Fin D → ℂ) → Fin n → ℂ} {V : Set (Fin D → ℂ)}
    (hV : IsOpen V) (hsd : DifferentiableOn ℂ s V) : AnalyticOnNhd ℂ s V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesOffDiscriminant».«analyticOnNhd_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_StokesOffDiscriminant_analyticOnNhd_of_differentiableOn_6a4255f10c53
