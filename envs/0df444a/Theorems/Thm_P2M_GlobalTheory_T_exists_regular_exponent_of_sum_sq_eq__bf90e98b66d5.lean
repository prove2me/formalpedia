-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_regular_exponent_of_sum_sq_eq__bf90e98b66d5
-- name    : P2M_GlobalTheory_T_exists_regular_exponent_of_sum_sq_eq__bf90e98b66d5
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:00.402202+00:00
-- url     : https://prove2.me/theorems/3d56ccb1-2da3-40d9-9d5d-509ad56fc765
-- title:
--   P2 M Global Theory T exists regular exponent of sum sq eq  bf90e98b66d5: P2 M Global Theory T exists regular exponent of sum sq eq  bf90e98b66d5
-- statement:
--   The P2 M Global Theory T exists regular exponent of sum sq eq  bf90e98b66d5 construction uses the P2 M Global Theory T exists regular exponent of sum sq eq  bf90e98b66d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularExponentOfSumSqEqStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularExponentOfSumSqEqStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularExponentOfSumSqEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularExponentOfSumSqEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_regular_exponent_of_sum_sq_eq__bf90e98b66d5 : ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d → (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) → ∑ k ∈ Finset.range (q ^ d - 1), a k ^ 2 = d → (∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l) → ∃ k : ℕ, a k ≠ 0 ∧ ∀ i : ℕ, 0 < i → i < d → ¬ k * q ^ i ≡ k [MOD q ^ d - 1] := by sorry

alias «GlobalTheory».«T».«exists_regular_exponent_of_sum_sq_eq'» := P2M_GlobalTheory_T_exists_regular_exponent_of_sum_sq_eq__bf90e98b66d5
