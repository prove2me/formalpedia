-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_toGeo_a_e5f916118ff1
-- name    : P2M_GroundTheory_Heights__Heights_HermLine_toGeo_a_e5f916118ff1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:53.53774+00:00
-- url     : https://prove2.me/theorems/4f0d3f10-ab60-49cb-a26b-f625aefcfbd7
-- title:
--   P2 M Ground Theory Heights  Heights Herm Line to Geo a e5f916118ff1: P2 M Ground Theory Heights  Heights Herm Line to Geo a e5f916118ff1
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Line to Geo a e5f916118ff1 construction uses the P2 M Ground Theory Heights  Heights Herm Line to Geo a e5f916118ff1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L115-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L115-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.HermLine

theorem P2M_GroundTheory_Heights__Heights_HermLine_toGeo_a_e5f916118ff1 (A : HermLine n) : A.toGeo.a = A.deg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermLine».«toGeo_a» := P2M_GroundTheory_Heights__Heights_HermLine_toGeo_a_e5f916118ff1
