-- Prove2me | Theorems.Thm_UpperTheory_T3_exists_three_primes_one_mod_le_rpow
-- name    : UpperTheory.T3.exists_three_primes_one_mod_le_rpow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:12:51.657805+00:00
-- url     : https://prove2.me/theorems/84890dcf-4ff3-497f-9477-c104849790a7
-- title:
--   T3: exists three primes one mod le rpow
-- statement:
--   The T3 construction uses the exists three primes one mod le rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/ExistsThreePrimesOneModLeRpow.lean#L10-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/ExistsThreePrimesOneModLeRpow.lean#L10-L70

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ExistsThreePrimesOneModLeRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Mem.An
open UpperTheory UpperTheory.T3

theorem UpperTheory.T3.exists_three_primes_one_mod_le_rpow :
    SmallOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧
      p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by sorry
