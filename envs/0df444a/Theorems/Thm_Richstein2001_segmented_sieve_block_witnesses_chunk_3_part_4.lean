-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_4
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:21:02.498764+00:00
-- url     : https://prove2.me/theorems/1f5e79da-627b-4e62-9735-471e5f8100bb
-- title:
--   Segmented sieve witnesses, block range 180000000-189999999
-- statement:
--   For each block index b in [180000000,190000000), every even integer in the block interval has a representation as a prime p ≤ 5569 plus a Goldbach sieve survivor q in the specified range. This is a subrange of Richstein's finite witness computation.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived block-range subgoal of Richstein2001.segmented_sieve_block_witnesses.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_3_part_4 (b : Nat) (hb : b < 400000001) (hlo : 180000000 ≤ b) (hhi : b < 190000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry
end Richstein2001
