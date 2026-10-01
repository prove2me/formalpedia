-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_3
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:21:08.462124+00:00
-- url     : https://prove2.me/theorems/773a72ea-d8a5-4d10-9867-75f1f242fb11
-- title:
--   Segmented sieve witnesses, block range 170000000-179999999
-- statement:
--   For each block index b in [170000000,180000000), every even integer in the block interval has a representation as a prime p ≤ 5569 plus a Goldbach sieve survivor q in the specified range. This is a subrange of Richstein's finite witness computation.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived block-range subgoal of Richstein2001.segmented_sieve_block_witnesses.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_3_part_3 (b : Nat) (hb : b < 400000001) (hlo : 170000000 ≤ b) (hhi : b < 180000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry
end Richstein2001
