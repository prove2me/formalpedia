-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralSection_nonzeroAt_of_noCommonZero_5dd630099693
-- name    : P2M_GroundTheory_Heights__Heights_IntegralSection_nonzeroAt_of_noCommonZero_5dd630099693
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:55:25.859837+00:00
-- url     : https://prove2.me/theorems/52e499cf-0512-4d26-9066-e357a56aad47
-- title:
--   P2 M Ground Theory Heights  Heights Integral Section nonzero At of no Common Zero 5dd630099693: P2 M Ground Theory Heights  Heights Integral Section nonzero At of no Common Zero 5dd630099693
-- statement:
--   The P2 M Ground Theory Heights  Heights Integral Section nonzero At of no Common Zero 5dd630099693 construction uses the P2 M Ground Theory Heights  Heights Integral Section nonzero At of no Common Zero 5dd630099693 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L494-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L494-L512

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

theorem P2M_GroundTheory_Heights__Heights_IntegralSection_nonzeroAt_of_noCommonZero_5dd630099693 {J : ℕ} (s : Fin J → IntegralSection P a) {y : Coord n → Ω}
    (hy : Geo.mCoordIdeal (ι := blockIdx n) y = P.ideal) (τ : AlgebraicClosure ℚ →+* ℂ)
    (h : IndefiniteRowSideFullHecke.HeightsSet.NoCommonZero (ι := blockIdx n) P.ideal y a fun j ↦ (s j).valueAt y) :
    ∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IntegralSection».«nonzeroAt_of_noCommonZero» := P2M_GroundTheory_Heights__Heights_IntegralSection_nonzeroAt_of_noCommonZero_5dd630099693
