-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_coprime_orderOf_pow_prime_pow__cf23029f3352
-- name    : P2M_GlobalTheory_T_exists_coprime_orderOf_pow_prime_pow__cf23029f3352
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:18.655845+00:00
-- url     : https://prove2.me/theorems/4b588612-b778-4b78-9036-905ea70292bb
-- title:
--   P2 M Global Theory T exists coprime order Of pow prime pow  cf23029f3352: P2 M Global Theory T exists coprime order Of pow prime pow  cf23029f3352
-- statement:
--   The P2 M Global Theory T exists coprime order Of pow prime pow  cf23029f3352 construction uses the P2 M Global Theory T exists coprime order Of pow prime pow  cf23029f3352 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsCoprimeOrderOfPowPrimePowStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsCoprimeOrderOfPowPrimePowStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCoprimeOrderOfPowPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCoprimeOrderOfPowPrimePowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_coprime_orderOf_pow_prime_pow__cf23029f3352 : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by sorry

alias «GlobalTheory».«T».«exists_coprime_orderOf_pow_prime_pow'» := P2M_GlobalTheory_T_exists_coprime_orderOf_pow_prime_pow__cf23029f3352
