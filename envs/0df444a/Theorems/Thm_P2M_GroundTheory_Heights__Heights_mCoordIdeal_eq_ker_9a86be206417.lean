-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mCoordIdeal_eq_ker_9a86be206417
-- name    : P2M_GroundTheory_Heights__Heights_mCoordIdeal_eq_ker_9a86be206417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:38.512807+00:00
-- url     : https://prove2.me/theorems/fd066df9-bb39-450b-8eb7-c77533a74a63
-- title:
--   P2 M Ground Theory Heights  Heights m Coord Ideal eq ker 9a86be206417: P2 M Ground Theory Heights  Heights m Coord Ideal eq ker 9a86be206417
-- statement:
--   The P2 M Ground Theory Heights  Heights m Coord Ideal eq ker 9a86be206417 construction uses the P2 M Ground Theory Heights  Heights m Coord Ideal eq ker 9a86be206417 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L167-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L167-L172

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

theorem P2M_GroundTheory_Heights__Heights_mCoordIdeal_eq_ker_9a86be206417 {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    Geo.mCoordIdeal (ι := blockIdx n) y =
      RingHom.ker (eval₂Hom (Int.castRingHom (MvPolynomial ι Ω)) fun v : Coord n ↦ C (y v) * X v.1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mCoordIdeal_eq_ker» := P2M_GroundTheory_Heights__Heights_mCoordIdeal_eq_ker_9a86be206417
