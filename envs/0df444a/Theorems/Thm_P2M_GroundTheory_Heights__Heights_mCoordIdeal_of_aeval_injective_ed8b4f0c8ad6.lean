-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mCoordIdeal_of_aeval_injective_ed8b4f0c8ad6
-- name    : P2M_GroundTheory_Heights__Heights_mCoordIdeal_of_aeval_injective_ed8b4f0c8ad6
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:54:38.351797+00:00
-- url     : https://prove2.me/theorems/2c5fe8bb-73f8-5cda-9367-c488a37c95a8
-- title:
--   P2 M Ground Theory Heights  Heights m Coord Ideal of aeval injective ed8b4f0c8ad6: P2 M Ground Theory Heights  Heights m Coord Ideal of aeval injective ed8b4f0c8ad6
-- statement:
--   The P2 M Ground Theory Heights  Heights m Coord Ideal of aeval injective ed8b4f0c8ad6 construction uses the P2 M Ground Theory Heights  Heights m Coord Ideal of aeval injective ed8b4f0c8ad6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L184-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L184-L194

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_mCoordIdeal_of_aeval_injective_ed8b4f0c8ad6 {Ω : Type} [Field Ω] (y : Coord n → Ω)
    (hy : Function.Injective (aeval y : MvPolynomial (Coord n) ℤ →ₐ[ℤ] Ω)) :
    Geo.mCoordIdeal (ι := blockIdx n) y = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mCoordIdeal_of_aeval_injective» := P2M_GroundTheory_Heights__Heights_mCoordIdeal_of_aeval_injective_ed8b4f0c8ad6
