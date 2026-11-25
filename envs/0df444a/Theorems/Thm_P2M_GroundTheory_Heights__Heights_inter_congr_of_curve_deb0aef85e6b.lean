-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_inter_congr_of_curve_deb0aef85e6b
-- name    : P2M_GroundTheory_Heights__Heights_inter_congr_of_curve_deb0aef85e6b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:06:39.542796+00:00
-- url     : https://prove2.me/theorems/0f02b770-39a9-4bd3-bd09-bc8e3c28a187
-- title:
--   P2 M Ground Theory Heights  Heights inter congr of curve deb0aef85e6b: P2 M Ground Theory Heights  Heights inter congr of curve deb0aef85e6b
-- statement:
--   The P2 M Ground Theory Heights  Heights inter congr of curve deb0aef85e6b construction uses the P2 M Ground Theory Heights  Heights inter congr of curve deb0aef85e6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L273-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L273-L329

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

theorem P2M_GroundTheory_Heights__Heights_inter_congr_of_curve_deb0aef85e6b
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (hII : Geo.IsIntersectionFamily II) {W : Ideal (MvPolynomial (Coord n) ℤ)}
    (hW : Geo.IsArithVar (ι := blockIdx n) W 1) {B B' : Geo.HermLine (blockIdx n)}
    (hB : Geo.IsSmoothHerm B) (hB' : Geo.IsSmoothHerm B') (ha : B.a = B'.a)
    (hh : ∀ z ∈ Geo.mcPts W, B.h z = B'.h z) : II W 1 ![B] = II W 1 ![B'] := by sorry

alias «GroundTheory».«Heights₂».«Heights».«inter_congr_of_curve» := P2M_GroundTheory_Heights__Heights_inter_congr_of_curve_deb0aef85e6b
