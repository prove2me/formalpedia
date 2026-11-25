-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HadamardPSDAux_le_of_diag_pos_7e09ecc94e55
-- name    : P2M_GroundTheory_Heights__Heights_HadamardPSDAux_le_of_diag_pos_7e09ecc94e55
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:18.867209+00:00
-- url     : https://prove2.me/theorems/47560353-8551-4650-8d08-93ec7639482c
-- title:
--   P2 M Ground Theory Heights  Heights Hadamard PSDAux le of diag pos 7e09ecc94e55: P2 M Ground Theory Heights  Heights Hadamard PSDAux le of diag pos 7e09ecc94e55
-- statement:
--   The P2 M Ground Theory Heights  Heights Hadamard PSDAux le of diag pos 7e09ecc94e55 construction uses the P2 M Ground Theory Heights  Heights Hadamard PSDAux le of diag pos 7e09ecc94e55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHadamardPSD.lean#L20-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHadamardPSD.lean#L20-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHadamardPSD
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
open Matrix Finset
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.HadamardPSDAux

theorem P2M_GroundTheory_Heights__Heights_HadamardPSDAux_le_of_diag_pos_7e09ecc94e55 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    (hpos : ∀ i, 0 < (A i i).re) : ‖A.det‖ ≤ ∏ i, ‖A i i‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HadamardPSDAux».«le_of_diag_pos» := P2M_GroundTheory_Heights__Heights_HadamardPSDAux_le_of_diag_pos_7e09ecc94e55
