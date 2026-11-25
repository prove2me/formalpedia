-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_flatCone_0f6d6e67785c
-- name    : P2M_GroundTheory_Heights__Heights_aeval_flatCone_0f6d6e67785c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:12:51.096532+00:00
-- url     : https://prove2.me/theorems/3f735e0c-5613-4f15-b387-c5f7ab76381a
-- title:
--   P2 M Ground Theory Heights  Heights aeval flat Cone 0f6d6e67785c: P2 M Ground Theory Heights  Heights aeval flat Cone 0f6d6e67785c
-- statement:
--   The P2 M Ground Theory Heights  Heights aeval flat Cone 0f6d6e67785c construction uses the P2 M Ground Theory Heights  Heights aeval flat Cone 0f6d6e67785c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L108-L111

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_aeval_flatCone_0f6d6e67785c {F : Type*} [CommRing F] (x : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    aeval (flatCone x) f = evalCone x f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«aeval_flatCone» := P2M_GroundTheory_Heights__Heights_aeval_flatCone_0f6d6e67785c
