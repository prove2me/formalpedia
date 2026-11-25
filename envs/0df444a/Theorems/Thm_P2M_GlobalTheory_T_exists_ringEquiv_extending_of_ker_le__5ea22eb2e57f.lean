-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_ringEquiv_extending_of_ker_le__5ea22eb2e57f
-- name    : P2M_GlobalTheory_T_exists_ringEquiv_extending_of_ker_le__5ea22eb2e57f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:37:36.850662+00:00
-- url     : https://prove2.me/theorems/ecc61f78-1192-437e-b956-c1f068cec738
-- title:
--   P2 M Global Theory T exists ring Equiv extending of ker le  5ea22eb2e57f: P2 M Global Theory T exists ring Equiv extending of ker le  5ea22eb2e57f
-- statement:
--   The P2 M Global Theory T exists ring Equiv extending of ker le  5ea22eb2e57f construction uses the P2 M Global Theory T exists ring Equiv extending of ker le  5ea22eb2e57f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingEquivExtendingOfKerLeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingEquivExtendingOfKerLeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingEquivExtendingOfKerLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingEquivExtendingOfKerLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_ringEquiv_extending_of_ker_le__5ea22eb2e57f : ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) → ∀ (R : Subring k) (J : Type) (α β : J → k), (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) → ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by sorry

alias «GlobalTheory».«T».«exists_ringEquiv_extending_of_ker_le'» := P2M_GlobalTheory_T_exists_ringEquiv_extending_of_ker_le__5ea22eb2e57f
