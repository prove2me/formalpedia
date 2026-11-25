-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_gram_det_change_of_basis__5b91eb961e07
-- name    : P2M_GlobalTheory_T_gram_det_change_of_basis__5b91eb961e07
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:28.546023+00:00
-- url     : https://prove2.me/theorems/01e44033-0148-5ce5-b93e-667e6f20ba11
-- title:
--   P2 M Global Theory T gram det change of basis  5b91eb961e07: P2 M Global Theory T gram det change of basis  5b91eb961e07
-- statement:
--   The P2 M Global Theory T gram det change of basis  5b91eb961e07 construction uses the P2 M Global Theory T gram det change of basis  5b91eb961e07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetChangeOfBasesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetChangeOfBasesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetChangeOfBases
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetChangeOfBasesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_gram_det_change_of_basis__5b91eb961e07 : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = W → LinearIndependent K u' → Submodule.span K (Set.range u') = W → ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by sorry

alias «GlobalTheory».«T».«gram_det_change_of_basis'» := P2M_GlobalTheory_T_gram_det_change_of_basis__5b91eb961e07
