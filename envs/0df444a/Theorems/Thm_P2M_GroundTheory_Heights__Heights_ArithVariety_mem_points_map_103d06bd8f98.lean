-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_map_103d06bd8f98
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_map_103d06bd8f98
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:24.200673+00:00
-- url     : https://prove2.me/theorems/9ab722fb-5e96-4174-9fa8-df448adaba91
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety mem points map 103d06bd8f98: P2 M Ground Theory Heights  Heights Arith Variety mem points map 103d06bd8f98
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety mem points map 103d06bd8f98 construction uses the P2 M Ground Theory Heights  Heights Arith Variety mem points map 103d06bd8f98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L376-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L376-L380

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {Ω : Type*} [Field Ω]
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_map_103d06bd8f98 (P : ArithVariety n) (τ : AlgebraicClosure ℚ →+* ℂ)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : x ∈ P.points (AlgebraicClosure ℚ)) :
    (fun k i ↦ τ (x k i)) ∈ P.points ℂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«mem_points_map» := P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_map_103d06bd8f98
