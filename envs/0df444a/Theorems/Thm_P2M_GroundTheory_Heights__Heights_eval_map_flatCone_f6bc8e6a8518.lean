-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518
-- name    : P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:57.984485+00:00
-- url     : https://prove2.me/theorems/f6964eee-a2a1-4d6c-8347-fa6037788931
-- title:
--   P2 M Ground Theory Heights  Heights eval map flat Cone f6bc8e6a8518: P2 M Ground Theory Heights  Heights eval map flat Cone f6bc8e6a8518
-- statement:
--   The P2 M Ground Theory Heights  Heights eval map flat Cone f6bc8e6a8518 construction uses the P2 M Ground Theory Heights  Heights eval map flat Cone f6bc8e6a8518 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L32-L35

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

theorem P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518 {F : Type*} [CommRing F] (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    eval (flatCone z) (map (Int.castRingHom F) f) = evalCone z f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_map_flatCone» := P2M_GroundTheory_Heights__Heights_eval_map_flatCone_f6bc8e6a8518
