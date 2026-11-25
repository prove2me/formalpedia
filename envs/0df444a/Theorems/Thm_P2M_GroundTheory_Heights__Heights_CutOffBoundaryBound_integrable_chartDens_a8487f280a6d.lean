-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_integrable_chartDens_a8487f280a6d
-- name    : P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_integrable_chartDens_a8487f280a6d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:18.223004+00:00
-- url     : https://prove2.me/theorems/963f8303-670d-4c47-aad6-99eeafe6aba9
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Boundary Bound integrable chart Dens a8487f280a6d: P2 M Ground Theory Heights  Heights Cut Off Boundary Bound integrable chart Dens a8487f280a6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Boundary Bound integrable chart Dens a8487f280a6d construction uses the P2 M Ground Theory Heights  Heights Cut Off Boundary Bound integrable chart Dens a8487f280a6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L80-L86

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

theorem P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_integrable_chartDens_a8487f280a6d (hM : ChartMassCompact.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : ContinuousOn f (zeroSet J))
    {ψ : Fin d → (Fin n → ℂ) → ℝ} (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i))
    (hc : HasCompactSupport f ∨ ∃ i, HasCompactSupport (ψ i)) : Integrable (chartDens J A f ψ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffBoundaryBound».«integrable_chartDens» := P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_integrable_chartDens_a8487f280a6d
