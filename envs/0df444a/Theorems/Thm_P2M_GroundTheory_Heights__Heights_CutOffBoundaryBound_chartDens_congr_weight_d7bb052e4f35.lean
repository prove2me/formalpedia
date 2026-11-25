-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_chartDens_congr_weight_d7bb052e4f35
-- name    : P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_chartDens_congr_weight_d7bb052e4f35
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:27.516106+00:00
-- url     : https://prove2.me/theorems/f2047c2e-9ee9-5807-80a5-393d3603824a
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Boundary Bound chart Dens congr weight d7bb052e4f35: P2 M Ground Theory Heights  Heights Cut Off Boundary Bound chart Dens congr weight d7bb052e4f35
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Boundary Bound chart Dens congr weight d7bb052e4f35 construction uses the P2 M Ground Theory Heights  Heights Cut Off Boundary Bound chart Dens congr weight d7bb052e4f35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L44-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
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
open GroundTheory.Heights₂.Heights.CutOffBoundaryBound
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_chartDens_congr_weight_d7bb052e4f35 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f f' : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) (h : ∀ x ∈ zeroSet J, f x = f' x) :
    chartDens J A f φ = chartDens J A f' φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffBoundaryBound».«chartDens_congr_weight» := P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_chartDens_congr_weight_d7bb052e4f35
