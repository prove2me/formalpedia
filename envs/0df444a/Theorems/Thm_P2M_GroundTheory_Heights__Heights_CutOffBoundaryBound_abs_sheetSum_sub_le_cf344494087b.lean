-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_abs_sheetSum_sub_le_cf344494087b
-- name    : P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_abs_sheetSum_sub_le_cf344494087b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:10.565953+00:00
-- url     : https://prove2.me/theorems/22ff9d81-f780-4214-99a4-52443ad75009
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Boundary Bound abs sheet Sum sub le cf344494087b: P2 M Ground Theory Heights  Heights Cut Off Boundary Bound abs sheet Sum sub le cf344494087b
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Boundary Bound abs sheet Sum sub le cf344494087b construction uses the P2 M Ground Theory Heights  Heights Cut Off Boundary Bound abs sheet Sum sub le cf344494087b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L53-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L53-L68

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

theorem P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_abs_sheetSum_sub_le_cf344494087b {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite)
    (T₁ T₂ P Q₁ Q₂ R₁ R₂ : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (a b c : ℝ)
    (h : ∀ x ∈ fibre J A y, ∀ s, IsSheetAt J A x s →
      |T₁ x s - T₂ x s| ≤ a * P x s + b * (Q₁ x s - Q₂ x s) + c * (R₁ x s - R₂ x s)) :
    |sheetSum J A T₁ y - sheetSum J A T₂ y| ≤ a * sheetSum J A P y +
      b * (sheetSum J A Q₁ y - sheetSum J A Q₂ y) + c * (sheetSum J A R₁ y - sheetSum J A R₂ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffBoundaryBound».«abs_sheetSum_sub_le» := P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_abs_sheetSum_sub_le_cf344494087b
