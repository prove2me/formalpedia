-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_hasSum_graded_of_mul_degree__c02842eb4fa7
-- name    : P2M_GlobalTheory_T_hasSum_graded_of_mul_degree__c02842eb4fa7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:22.326894+00:00
-- url     : https://prove2.me/theorems/fb17b222-0b98-5820-9d41-284c11406418
-- title:
--   P2 M Global Theory T has Sum graded of mul degree  c02842eb4fa7: P2 M Global Theory T has Sum graded of mul degree  c02842eb4fa7
-- statement:
--   The P2 M Global Theory T has Sum graded of mul degree  c02842eb4fa7 construction uses the P2 M Global Theory T has Sum graded of mul degree  c02842eb4fa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HasSumGradedOfMulDegreeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HasSumGradedOfMulDegreeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumGradedOfMulDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumGradedOfMulDegreeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_hasSum_graded_of_mul_degree__c02842eb4fa7 : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) [AddCommGroup X] (Rel : ℕ → (X → C) → C → Prop) (n k : ℕ), 1 ≤ n → 1 ≤ k → (∀ (l l' : ℕ) (a a' : X → C) (c c' : C), 1 ≤ l → 1 ≤ l' → Rel l a c → Rel l' a' c' → ∃ a'', Rel (l + l') a'' (c * c') ∧ ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) → (∃ κ : C, κ ≠ 0 ∧ ∀ a c, Rel (n * k) a c → HasSum a (κ * c)) → ∃ u : C, u ≠ 0 ∧ ∀ a c, Rel k a c → Summable a → HasSum a (u * c) := by sorry

alias «GlobalTheory».«T».«hasSum_graded_of_mul_degree'» := P2M_GlobalTheory_T_hasSum_graded_of_mul_degree__c02842eb4fa7
