-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HadamardPSDAux_det_eq_zero_of_diag_eq_zero_459d5de6f62b
-- name    : P2M_GroundTheory_Heights__Heights_HadamardPSDAux_det_eq_zero_of_diag_eq_zero_459d5de6f62b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:10.688481+00:00
-- url     : https://prove2.me/theorems/111b1904-46f7-4ddd-a956-ee13988cf911
-- title:
--   P2 M Ground Theory Heights  Heights Hadamard PSDAux det eq zero of diag eq zero 459d5de6f62b: P2 M Ground Theory Heights  Heights Hadamard PSDAux det eq zero of diag eq zero 459d5de6f62b
-- statement:
--   The P2 M Ground Theory Heights  Heights Hadamard PSDAux det eq zero of diag eq zero 459d5de6f62b construction uses the P2 M Ground Theory Heights  Heights Hadamard PSDAux det eq zero of diag eq zero 459d5de6f62b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHadamardPSD.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHadamardPSD.lean#L12-L18

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

theorem P2M_GroundTheory_Heights__Heights_HadamardPSDAux_det_eq_zero_of_diag_eq_zero_459d5de6f62b {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef)
    {i : Fin n} (hi : A i i = 0) : A.det = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HadamardPSDAux».«det_eq_zero_of_diag_eq_zero» := P2M_GroundTheory_Heights__Heights_HadamardPSDAux_det_eq_zero_of_diag_eq_zero_459d5de6f62b
