-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_gram_det_ne_zero_of_ker_orth__c48c67bfcbef
-- name    : P2M_GlobalTheory_T_gram_det_ne_zero_of_ker_orth__c48c67bfcbef
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:03.413138+00:00
-- url     : https://prove2.me/theorems/35fd6b26-d115-4145-8440-5d1ddb6c84da
-- title:
--   P2 M Global Theory T gram det ne zero of ker orth  c48c67bfcbef: P2 M Global Theory T gram det ne zero of ker orth  c48c67bfcbef
-- statement:
--   The P2 M Global Theory T gram det ne zero of ker orth  c48c67bfcbef construction uses the P2 M Global Theory T gram det ne zero of ker orth  c48c67bfcbef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetNeZeroOfKerOrthStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetNeZeroOfKerOrthStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetNeZeroOfKerOrth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetNeZeroOfKerOrthStatement
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

theorem P2M_GlobalTheory_T_gram_det_ne_zero_of_ker_orth__c48c67bfcbef : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A) → (∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) → (∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) → (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by sorry

alias «GlobalTheory».«T».«gram_det_ne_zero_of_ker_orth'» := P2M_GlobalTheory_T_gram_det_ne_zero_of_ker_orth__c48c67bfcbef
