-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_isUnit_det_submatrix_of_mem_blockUpper__fc1b51b4478e
-- name    : P2M_GroundTheory_Automorphic_Parabolic_isUnit_det_submatrix_of_mem_blockUpper__fc1b51b4478e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:49.028102+00:00
-- url     : https://prove2.me/theorems/dd7515f4-da70-45a4-a27f-59c1a7796602
-- title:
--   P2 M Ground Theory Automorphic Parabolic is Unit det submatrix of mem block Upper  fc1b51b4478e: P2 M Ground Theory Automorphic Parabolic is Unit det submatrix of mem block Upper  fc1b51b4478e
-- statement:
--   The P2 M Ground Theory Automorphic Parabolic is Unit det submatrix of mem block Upper  fc1b51b4478e construction uses the P2 M Ground Theory Automorphic Parabolic is Unit det submatrix of mem block Upper  fc1b51b4478e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L131-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L131-L139

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}

theorem P2M_GroundTheory_Automorphic_Parabolic_isUnit_det_submatrix_of_mem_blockUpper__fc1b51b4478e {q : GL (Fin n) F} (hq : q ∈ blockUpper F n γ)
    (b : ℕ) :
    IsUnit ((q : Matrix (Fin n) (Fin n) F).submatrix (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))
      (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))).det := by sorry

alias «GroundTheory».«Automorphic».«Parabolic».«isUnit_det_submatrix_of_mem_blockUpper'» := P2M_GroundTheory_Automorphic_Parabolic_isUnit_det_submatrix_of_mem_blockUpper__fc1b51b4478e
