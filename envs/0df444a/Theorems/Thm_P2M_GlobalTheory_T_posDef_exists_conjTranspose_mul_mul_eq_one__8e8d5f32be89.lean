-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_posDef_exists_conjTranspose_mul_mul_eq_one__8e8d5f32be89
-- name    : P2M_GlobalTheory_T_posDef_exists_conjTranspose_mul_mul_eq_one__8e8d5f32be89
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:28.82537+00:00
-- url     : https://prove2.me/theorems/7da8f31b-8b88-441c-9529-e7927cc0058e
-- title:
--   P2 M Global Theory T pos Def exists conj Transpose mul mul eq one  8e8d5f32be89: P2 M Global Theory T pos Def exists conj Transpose mul mul eq one  8e8d5f32be89
-- statement:
--   The P2 M Global Theory T pos Def exists conj Transpose mul mul eq one  8e8d5f32be89 construction uses the P2 M Global Theory T pos Def exists conj Transpose mul mul eq one  8e8d5f32be89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefExistsConjTransposeMulMulEqOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosDefExistsConjTransposeMulMulEqOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefExistsConjTransposeMulMulEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefExistsConjTransposeMulMulEqOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_posDef_exists_conjTranspose_mul_mul_eq_one__8e8d5f32be89 : ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef → ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by sorry

alias «GlobalTheory».«T».«posDef_exists_conjTranspose_mul_mul_eq_one'» := P2M_GlobalTheory_T_posDef_exists_conjTranspose_mul_mul_eq_one__8e8d5f32be89
