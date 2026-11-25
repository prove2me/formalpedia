-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReadsMul_mem_mCoordIdeal_a1b8fcafa902
-- name    : P2M_GroundTheory_Heights__Heights_ReadsMul_mem_mCoordIdeal_a1b8fcafa902
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:23:07.206468+00:00
-- url     : https://prove2.me/theorems/795792b9-e387-51a3-b4d5-1b86184a99a3
-- title:
--   P2 M Ground Theory Heights  Heights Reads Mul mem m Coord Ideal a1b8fcafa902: P2 M Ground Theory Heights  Heights Reads Mul mem m Coord Ideal a1b8fcafa902
-- statement:
--   The P2 M Ground Theory Heights  Heights Reads Mul mem m Coord Ideal a1b8fcafa902 construction uses the P2 M Ground Theory Heights  Heights Reads Mul mem m Coord Ideal a1b8fcafa902 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PReadsMul.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PReadsMul.lean#L34-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PReadsMul
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
noncomputable section
open GroundTheory.Heights₂.Heights.ReadsMul
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ReadsMul_mem_mCoordIdeal_a1b8fcafa902 {Ω : Type} [Field Ω] (y : Coord n → Ω) {g : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g d) (h0 : aeval y g = 0) :
    g ∈ Geo.mCoordIdeal (ι := blockIdx n) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ReadsMul».«mem_mCoordIdeal» := P2M_GroundTheory_Heights__Heights_ReadsMul_mem_mCoordIdeal_a1b8fcafa902
