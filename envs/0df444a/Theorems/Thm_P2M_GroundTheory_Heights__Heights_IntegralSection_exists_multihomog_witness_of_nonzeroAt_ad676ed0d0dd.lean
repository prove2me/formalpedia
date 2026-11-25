-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralSection_exists_multihomog_witness_of_nonzeroAt_ad676ed0d0dd
-- name    : P2M_GroundTheory_Heights__Heights_IntegralSection_exists_multihomog_witness_of_nonzeroAt_ad676ed0d0dd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:27:13.43532+00:00
-- url     : https://prove2.me/theorems/4c62b022-7f94-4c01-8a1a-b983db15606b
-- title:
--   P2 M Ground Theory Heights  Heights Integral Section exists multihomog witness of nonzero At ad676ed0d0dd: P2 M Ground Theory Heights  Heights Integral Section exists multihomog witness of nonzero At
-- statement:
--   The P2 M Ground Theory Heights  Heights Integral Section exists multihomog witness of nonzero At ad676ed0d0dd construction uses the P2 M Ground Theory Heights  Heights Integral Section exists multihomog witness of nonzero At ad676ed0d0dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L514-L530
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L514-L530

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
open GroundTheory.Heights₂.Heights.IntegralSection
variable {P : ArithVariety n} {a : ι → ℤ}

theorem P2M_GroundTheory_Heights__Heights_IntegralSection_exists_multihomog_witness_of_nonzeroAt_ad676ed0d0dd (s : IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) (τ : AlgebraicClosure ℚ →+* ℂ)
    {x : Cone n (AlgebraicClosure ℚ)} (hxs : s.NonzeroAt x) :
    ∃ (dg dh : ι → ℕ) (g h : MvPolynomial (Coord n) ℤ),
      Geo.IsMultiHomog (ι := blockIdx n) g dg ∧ Geo.IsMultiHomog (ι := blockIdx n) h dh ∧
      (∀ k, (dg k : ℤ) = dh k + a k) ∧ aeval y g = s.valueAt y * aeval y h ∧
      eval (flatCone fun k i ↦ τ (x k i)) (map (Int.castRingHom ℂ) g) ≠ 0 ∧
      eval (flatCone fun k i ↦ τ (x k i)) (map (Int.castRingHom ℂ) h) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IntegralSection».«exists_multihomog_witness_of_nonzeroAt» := P2M_GroundTheory_Heights__Heights_IntegralSection_exists_multihomog_witness_of_nonzeroAt_ad676ed0d0dd
