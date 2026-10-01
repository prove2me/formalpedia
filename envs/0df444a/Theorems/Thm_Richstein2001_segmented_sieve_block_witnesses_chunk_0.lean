-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_0
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:15.474847+00:00
-- url     : https://prove2.me/theorems/7f369cf3-c96b-4dd2-9848-5cc5e96dab71
-- title:
--   Segmented sieve witnesses, block range 0-49999999
-- statement:
--   For every block index b in [0,50000000), and every even integer n in the corresponding interval, there are a prime p <= 5569 and a sieve survivor q in the specified range such that n = p + q. This is one contiguous segment of the finite witness computation for Richstein's Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived block-range subgoal of Richstein2001.segmented_sieve_block_witnesses.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_0 (b : ℕ) (hb : b < 400000001)
    (hlo : 0 ≤ b) (hhi : b < 50000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry

end Richstein2001
