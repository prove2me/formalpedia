-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_summable_rpow_of_fibre_card_le__c55443d5c67b
-- name    : P2M_GlobalTheory_T_summable_rpow_of_fibre_card_le__c55443d5c67b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:47.829315+00:00
-- url     : https://prove2.me/theorems/397a7aad-39d6-445b-b4a3-6e892965854d
-- title:
--   P2 M Global Theory T summable rpow of fibre card le  c55443d5c67b: P2 M Global Theory T summable rpow of fibre card le  c55443d5c67b
-- statement:
--   The P2 M Global Theory T summable rpow of fibre card le  c55443d5c67b construction uses the P2 M Global Theory T summable rpow of fibre card le  c55443d5c67b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SummableRpowOfFibreCardLeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SummableRpowOfFibreCardLeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SummableRpowOfFibreCardLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SummableRpowOfFibreCardLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_summable_rpow_of_fibre_card_le__c55443d5c67b : ∀ (ι : Type) (n : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ) (h : ι → ℝ), 1 < b → (n : ℝ) < t → (∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹) → (∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) → (T.card : ℝ) ≤ C * ∏ i, b ^ (n * m i)) → Summable fun q => h q ^ t := by sorry

alias «GlobalTheory».«T».«summable_rpow_of_fibre_card_le'» := P2M_GlobalTheory_T_summable_rpow_of_fibre_card_le__c55443d5c67b
