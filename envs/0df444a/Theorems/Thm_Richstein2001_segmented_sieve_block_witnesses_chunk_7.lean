-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:14.921667+00:00
-- url     : https://prove2.me/theorems/7e8d5cdf-fe4d-4b64-9ca3-b70bc8245766
-- title:
--   Segmented sieve witnesses, block range 350000000-399999999
-- statement:
--   For every block index b in [350000000,400000000), and every even integer n in the corresponding interval, there are a prime p <= 5569 and a sieve survivor q in the specified range such that n = p + q. This is one contiguous segment of the finite witness computation for Richstein's Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived block-range subgoal of Richstein2001.segmented_sieve_block_witnesses.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_7 (b : ℕ) (hb : b < 400000001)
    (hlo : 350000000 ≤ b) (hhi : b < 400000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry

end Richstein2001
