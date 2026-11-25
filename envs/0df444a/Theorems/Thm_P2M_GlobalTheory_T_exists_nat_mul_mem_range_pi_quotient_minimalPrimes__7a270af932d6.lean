-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_nat_mul_mem_range_pi_quotient_minimalPrimes__7a270af932d6
-- name    : P2M_GlobalTheory_T_exists_nat_mul_mem_range_pi_quotient_minimalPrimes__7a270af932d6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:05.744516+00:00
-- url     : https://prove2.me/theorems/1383cc63-99ac-44d6-a537-24aaf55f3425
-- title:
--   P2 M Global Theory T exists nat mul mem range pi quotient minimal Primes  7a270af932d6: P2 M Global Theory T exists nat mul mem range pi quotient minimal Primes  7a270af932d6
-- statement:
--   The P2 M Global Theory T exists nat mul mem range pi quotient minimal Primes  7a270af932d6 construction uses the P2 M Global Theory T exists nat mul mem range pi quotient minimal Primes  7a270af932d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNatMulMemRangePiQuotientMinimalPrimesStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNatMulMemRangePiQuotientMinimalPrimesStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatMulMemRangePiQuotientMinimalPrimes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatMulMemRangePiQuotientMinimalPrimesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_nat_mul_mem_range_pi_quotient_minimalPrimes__7a270af932d6 : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧ ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)), (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈ (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by sorry

alias «GlobalTheory».«T».«exists_nat_mul_mem_range_pi_quotient_minimalPrimes'» := P2M_GlobalTheory_T_exists_nat_mul_mem_range_pi_quotient_minimalPrimes__7a270af932d6
