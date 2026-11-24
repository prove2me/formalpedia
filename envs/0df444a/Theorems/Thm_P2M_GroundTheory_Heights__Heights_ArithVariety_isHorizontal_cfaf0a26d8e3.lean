-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_isHorizontal_cfaf0a26d8e3
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_isHorizontal_cfaf0a26d8e3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:47:57.661157+00:00
-- url     : https://prove2.me/theorems/786fbd69-b45d-4f09-8f82-c42f12d94288
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety is Horizontal cfaf0a26d8e3: P2 M Ground Theory Heights  Heights Arith Variety is Horizontal cfaf0a26d8e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety is Horizontal cfaf0a26d8e3 construction uses the P2 M Ground Theory Heights  Heights Arith Variety is Horizontal cfaf0a26d8e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L77-L81

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

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_isHorizontal_cfaf0a26d8e3 (P : ArithVariety n) :
    Geo.IsHorizontal (ι := blockIdx n) P.ideal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«isHorizontal» := P2M_GroundTheory_Heights__Heights_ArithVariety_isHorizontal_cfaf0a26d8e3
