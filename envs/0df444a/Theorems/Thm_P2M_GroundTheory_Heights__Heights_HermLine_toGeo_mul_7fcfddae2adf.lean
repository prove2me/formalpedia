-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_toGeo_mul_7fcfddae2adf
-- name    : P2M_GroundTheory_Heights__Heights_HermLine_toGeo_mul_7fcfddae2adf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:21:07.505586+00:00
-- url     : https://prove2.me/theorems/461f1cd6-2666-5dba-98d4-66e1bf51c69c
-- title:
--   P2 M Ground Theory Heights  Heights Herm Line to Geo mul 7fcfddae2adf: P2 M Ground Theory Heights  Heights Herm Line to Geo mul 7fcfddae2adf
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Line to Geo mul 7fcfddae2adf construction uses the P2 M Ground Theory Heights  Heights Herm Line to Geo mul 7fcfddae2adf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L138-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L138-L142

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

theorem P2M_GroundTheory_Heights__Heights_HermLine_toGeo_mul_7fcfddae2adf (A B : HermLine n) : (A.mul B).toGeo = A.toGeo.tensor B.toGeo := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermLine».«toGeo_mul» := P2M_GroundTheory_Heights__Heights_HermLine_toGeo_mul_7fcfddae2adf
