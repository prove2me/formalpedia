-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_pos_mul_extend_int_linearForm__1f996f723b45
-- name    : P2M_GlobalTheory_T_exists_pos_mul_extend_int_linearForm__1f996f723b45
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:17.167619+00:00
-- url     : https://prove2.me/theorems/a71b49ee-8d81-5407-a711-efa7065b96da
-- title:
--   P2 M Global Theory T exists pos mul extend int linear Form  1f996f723b45: P2 M Global Theory T exists pos mul extend int linear Form  1f996f723b45
-- statement:
--   The P2 M Global Theory T exists pos mul extend int linear Form  1f996f723b45 construction uses the P2 M Global Theory T exists pos mul extend int linear Form  1f996f723b45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPosMulExtendIntLinearFormStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPosMulExtendIntLinearFormStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPosMulExtendIntLinearForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPosMulExtendIntLinearFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_pos_mul_extend_int_linearForm__1f996f723b45 : ∀ (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ), ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by sorry

alias «GlobalTheory».«T».«exists_pos_mul_extend_int_linearForm'» := P2M_GlobalTheory_T_exists_pos_mul_extend_int_linearForm__1f996f723b45
