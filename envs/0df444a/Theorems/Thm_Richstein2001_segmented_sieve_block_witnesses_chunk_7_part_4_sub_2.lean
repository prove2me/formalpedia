-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_4_sub_2
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_4_sub_2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:53:55.545151+00:00
-- url     : https://prove2.me/theorems/90096802-bbd3-4520-9aca-0eccc2c0c00a
-- title:
--   Segmented sieve witnesses, subrange 382000000-383999999
-- statement:
--   For every block index in [382000000,384000000), each even integer in its associated interval has a representation as a prime at most 5569 plus a survivor for the specified sieve. This is one subrange in a decomposition of the 380000000-389999999 range.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; subrange of Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_4.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_7_part_4_sub_2 (b : ℕ) (hb : b < 400000001)
    (hlo : 382000000 ≤ b) (hhi : b < 384000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry

end Richstein2001
