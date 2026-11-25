-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_anti_2b5a3c1121df
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_anti_2b5a3c1121df
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:25:33.447906+00:00
-- url     : https://prove2.me/theorems/b116ce49-9e5b-4172-a2b2-ec1696beb65e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc anti 2b5a3c1121df: P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc anti 2b5a3c1121df
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc anti 2b5a3c1121df construction uses the P2 M Ground Theory Heights  Heights Field Numbers deg Zero Loc anti 2b5a3c1121df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalLengthSum.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsSemilocalLengthSum.lean#L13-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_anti_2b5a3c1121df {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) [P.IsPrime] {𝒲₁ 𝒲₂ : Set (Ideal (MRing ι F))} (h𝒲 : 𝒲₁ ⊆ 𝒲₂) :
    degZeroLoc P 𝒲₂ ≤ degZeroLoc P 𝒲₁ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«degZeroLoc_anti» := P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_anti_2b5a3c1121df
