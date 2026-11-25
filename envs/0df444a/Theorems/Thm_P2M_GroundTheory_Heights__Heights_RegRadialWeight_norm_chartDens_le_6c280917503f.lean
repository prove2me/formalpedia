-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegRadialWeight_norm_chartDens_le_6c280917503f
-- name    : P2M_GroundTheory_Heights__Heights_RegRadialWeight_norm_chartDens_le_6c280917503f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:19:28.888261+00:00
-- url     : https://prove2.me/theorems/400d05ff-7394-4cae-894b-30f8d46c8354
-- title:
--   P2 M Ground Theory Heights  Heights Reg Radial Weight norm chart Dens le 6c280917503f: P2 M Ground Theory Heights  Heights Reg Radial Weight norm chart Dens le 6c280917503f
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Radial Weight norm chart Dens le 6c280917503f construction uses the P2 M Ground Theory Heights  Heights Reg Radial Weight norm chart Dens le 6c280917503f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L166-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegRadialWeight.lean#L166-L174

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

theorem P2M_GroundTheory_Heights__Heights_RegRadialWeight_norm_chartDens_le_6c280917503f {D : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin D) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin D → (Fin n → ℂ) → ℝ) (y : Fin D → ℂ) :
    ‖chartDens J A f φ y‖ ≤ chartAbsDens J A f φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegRadialWeight».«norm_chartDens_le» := P2M_GroundTheory_Heights__Heights_RegRadialWeight_norm_chartDens_le_6c280917503f
