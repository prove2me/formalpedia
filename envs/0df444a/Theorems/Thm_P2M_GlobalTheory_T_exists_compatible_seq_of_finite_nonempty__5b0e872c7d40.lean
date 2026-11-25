-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_compatible_seq_of_finite_nonempty__5b0e872c7d40
-- name    : P2M_GlobalTheory_T_exists_compatible_seq_of_finite_nonempty__5b0e872c7d40
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:20.962495+00:00
-- url     : https://prove2.me/theorems/b834fad8-4341-48a0-befc-2c4997db5ffc
-- title:
--   P2 M Global Theory T exists compatible seq of finite nonempty  5b0e872c7d40: P2 M Global Theory T exists compatible seq of finite nonempty  5b0e872c7d40
-- statement:
--   The P2 M Global Theory T exists compatible seq of finite nonempty  5b0e872c7d40 construction uses the P2 M Global Theory T exists compatible seq of finite nonempty  5b0e872c7d40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompatibleSeqOfFiniteNonemptyStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompatibleSeqOfFiniteNonemptyStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleSeqOfFiniteNonempty
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleSeqOfFiniteNonemptyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_compatible_seq_of_finite_nonempty__5b0e872c7d40 : ∀ (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n)), (∀ n, (Y n).Finite) → (∀ n, (Y n).Nonempty) → (∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) → ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by sorry

alias «GlobalTheory».«T».«exists_compatible_seq_of_finite_nonempty'» := P2M_GlobalTheory_T_exists_compatible_seq_of_finite_nonempty__5b0e872c7d40
