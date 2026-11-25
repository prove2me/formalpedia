-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_two_mul_le_add_div_264c0a734aca
-- name    : P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_two_mul_le_add_div_264c0a734aca
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:41.126926+00:00
-- url     : https://prove2.me/theorems/d872a6a1-1ca1-535a-94b2-5dd74de83de4
-- title:
--   P2 M Ground Theory Heights  Heights Cut Off Boundary Bound two mul le add div 264c0a734aca: P2 M Ground Theory Heights  Heights Cut Off Boundary Bound two mul le add div 264c0a734aca
-- statement:
--   The P2 M Ground Theory Heights  Heights Cut Off Boundary Bound two mul le add div 264c0a734aca construction uses the P2 M Ground Theory Heights  Heights Cut Off Boundary Bound two mul le add div 264c0a734aca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffBoundaryBound.lean#L128-L133

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

theorem P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_two_mul_le_add_div_264c0a734aca {t : ℝ} (ht : 0 < t) (u v : ℝ) : 2 * u * v ≤ t * u ^ 2 + v ^ 2 / t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CutOffBoundaryBound».«two_mul_le_add_div» := P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_two_mul_le_add_div_264c0a734aca
