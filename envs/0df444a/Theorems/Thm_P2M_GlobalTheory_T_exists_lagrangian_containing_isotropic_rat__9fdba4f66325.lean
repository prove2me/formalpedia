-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_lagrangian_containing_isotropic_rat__9fdba4f66325
-- name    : P2M_GlobalTheory_T_exists_lagrangian_containing_isotropic_rat__9fdba4f66325
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:28.721605+00:00
-- url     : https://prove2.me/theorems/a787a02d-9e8b-4be6-84ac-dde2a9453b93
-- title:
--   P2 M Global Theory T exists lagrangian containing isotropic rat  9fdba4f66325: P2 M Global Theory T exists lagrangian containing isotropic rat  9fdba4f66325
-- statement:
--   The P2 M Global Theory T exists lagrangian containing isotropic rat  9fdba4f66325 construction uses the P2 M Global Theory T exists lagrangian containing isotropic rat  9fdba4f66325 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLagrangianContainingIsotropicRatStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLagrangianContainingIsotropicRatStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLagrangianContainingIsotropicRat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLagrangianContainingIsotropicRatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_lagrangian_containing_isotropic_rat__9fdba4f66325 : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (I : Submodule ℚ (Fin r → ℚ)), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ x ∈ I, ∀ y ∈ I, x ⬝ᵥ Mq *ᵥ y = 0) → ∃ L : Submodule ℚ (Fin r → ℚ), I ≤ L ∧ (∀ x ∈ L, ∀ y ∈ L, x ⬝ᵥ Mq *ᵥ y = 0) ∧ Module.finrank ℚ L = g := by sorry

alias «GlobalTheory».«T».«exists_lagrangian_containing_isotropic_rat'» := P2M_GlobalTheory_T_exists_lagrangian_containing_isotropic_rat__9fdba4f66325
