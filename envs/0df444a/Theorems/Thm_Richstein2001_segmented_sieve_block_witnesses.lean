-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses
-- name    : Richstein2001.segmented_sieve_block_witnesses
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T12:55:53.124814+00:00
-- url     : https://prove2.me/theorems/546bd1bc-25fc-4842-a638-3fa94b03fb3a
-- title:
--   Per-number witnesses for each segmented sieve block
-- statement:
--   For each block index b in the Richstein range, every even integer in that block has a witness representation n = p + q, where p is prime and at most 5569 and q survives sieving by all primes through 20,000,000 in the specified block-dependent interval. These witnesses are the certificate-level data needed to verify each finite block.
-- source:
--   Certificate-level decomposition of Richstein2001.segmented_sieve_coverage; J. Richstein, Verifying the Goldbach conjecture up to 4·10^14, Math. Comp. 70 (2001), 1745–1749. The block interface follows the target formalization.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses (b : ℕ) (hb : b < 400000001) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry
end Richstein2001
