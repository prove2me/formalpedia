-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_final_bound_c07343cad33a
-- name    : P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_final_bound_c07343cad33a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:04.288711+00:00
-- url     : https://prove2.me/theorems/7b8c3281-ce86-5da1-8157-29f075644d63
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Boundary Bound final bound c07343cad33a: P2 M Ground Theory Heights  Heights Cut Off Boundary Bound final bound c07343cad33a
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Boundary Bound final bound c07343cad33a construction uses the P2 M Ground Theory Heights  Heights Cut Off Boundary Bound final bound c07343cad33a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L156-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L156-L193

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

theorem P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_final_bound_c07343cad33a {X M C aI E Φ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ aI)
    (h : ∀ t > 0, X ≤ M * aI + C * t * E + C / t * Φ) :
    X ≤ max M (2 * C * √(max Φ 1)) * (aI + √E) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffBoundaryBound».«final_bound» := P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_final_bound_c07343cad33a
