-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_1_upper_half
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_1_upper_half
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:05:51.06212+00:00
-- url     : https://prove2.me/theorems/d5f1b9fa-3056-444e-b6e5-e33a2b86fb7b
-- title:
--   Chunk 3 part 1 upper_half
-- statement:
--   For each block index from 150,000,000 through 159,999,999, every even integer in the final 500,000 positions of the block has the required prime plus sieve-survivor representation.
-- source:
--   Subrange of Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_1; Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_3_part_1_upper_half
    (b : Nat) (hb : b < 400000001) (hlo : 150000000 ≤ b)
    (hhi : b < 160000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      b * 1000000 + 500000 ≤ n ->
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry
end Richstein2001
