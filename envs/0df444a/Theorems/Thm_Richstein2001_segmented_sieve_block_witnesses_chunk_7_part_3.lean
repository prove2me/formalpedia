-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_3
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:37:54.036909+00:00
-- url     : https://prove2.me/theorems/4df727ca-c5ef-498c-80ed-455193194233
-- title:
--   Segmented sieve witnesses, block range 370000000-379999999
-- statement:
--   For each block index b in [370000000,380000000), every even integer in the associated interval has a representation as a prime p at most 5569 plus a survivor q for the specified sieve. This is a subrange of the finite witness computation in Richstein's Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; a 10-million-block-index partition of Richstein2001.segmented_sieve_block_witnesses_chunk_7.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_7_part_3 (b : ℕ) (hb : b < 400000001)
    (hlo : 370000000 ≤ b) (hhi : b < 380000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry

end Richstein2001
