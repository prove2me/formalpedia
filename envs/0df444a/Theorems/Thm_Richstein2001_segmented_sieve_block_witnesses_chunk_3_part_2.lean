-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_2
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:21:05.050918+00:00
-- url     : https://prove2.me/theorems/25450e99-fa3a-46e2-af08-2f3d7f620b96
-- title:
--   Segmented sieve witnesses, block range 160000000-169999999
-- statement:
--   For each block index b in [160000000,170000000), every even integer in the block interval has a representation as a prime p ≤ 5569 plus a Goldbach sieve survivor q in the specified range. This is a subrange of Richstein's finite witness computation.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived block-range subgoal of Richstein2001.segmented_sieve_block_witnesses.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_3_part_2 (b : Nat) (hb : b < 400000001) (hlo : 160000000 ≤ b) (hhi : b < 170000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry
end Richstein2001
