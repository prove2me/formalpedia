-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_analyticAt_of_isSheetAt_53bfd87cf7f8
-- name    : P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_analyticAt_of_isSheetAt_53bfd87cf7f8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:14.381524+00:00
-- url     : https://prove2.me/theorems/a638e8d3-e0cc-47af-8557-d54b373b88de
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Boundary Bound analytic At of is Sheet At 53bfd87cf7f8: P2 M Ground Theory Heights  Heights Cut Off Boundary Bound analytic At of is Sheet At 53bfd87cf7f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Boundary Bound analytic At of is Sheet At 53bfd87cf7f8 construction uses the P2 M Ground Theory Heights  Heights Cut Off Boundary Bound analytic At of is Sheet At 53bfd87cf7f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L23-L34

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

theorem P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_analyticAt_of_isSheetAt_53bfd87cf7f8 {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) : AnalyticAt ℂ s (A *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffBoundaryBound».«analyticAt_of_isSheetAt» := P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_analyticAt_of_isSheetAt_53bfd87cf7f8
