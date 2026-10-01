-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:20.136314+00:00
-- url     : https://prove2.me/theorems/e10029bc-fa7c-41a6-b4fa-7da34287caf1
-- title:
--   Segmented sieve witnesses, block range 200000000-249999999
-- statement:
--   For every block index b in [200000000,250000000), and every even integer n in the corresponding interval, there are a prime p <= 5569 and a sieve survivor q in the specified range such that n = p + q. This is one contiguous segment of the finite witness computation for Richstein's Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived block-range subgoal of Richstein2001.segmented_sieve_block_witnesses.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_4 (b : ℕ) (hb : b < 400000001)
    (hlo : 200000000 ≤ b) (hhi : b < 250000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry

end Richstein2001
