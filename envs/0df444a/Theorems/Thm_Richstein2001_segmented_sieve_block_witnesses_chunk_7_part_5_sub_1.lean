-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_5_sub_1
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5_sub_1
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T14:09:16.053+00:00
-- url     : https://prove2.me/theorems/06411385-3ac3-453c-b217-58bbbaf66d06
-- title:
--   Segmented sieve witnesses, subrange 390000000-391999999
-- statement:
--   For every block index in [390000000,392000000), each even integer in its associated interval has a representation as a prime at most 5569 plus a survivor for the specified sieve. This is one subrange in a decomposition of the 390000000-399999999 range.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; subrange of Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_7_part_5_sub_1 (b : ℕ) (hb : b < 400000001)
    (hlo : 390000000 ≤ b) (hhi : b < 392000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry

end Richstein2001
