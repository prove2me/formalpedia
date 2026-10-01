-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_5
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:37:56.178026+00:00
-- url     : https://prove2.me/theorems/89dd0936-0073-4fc1-a4f7-4b78e3bce7ec
-- title:
--   Segmented sieve witnesses, block range 390000000-399999999
-- statement:
--   For each block index b in [390000000,400000000), every even integer in the associated interval has a representation as a prime p at most 5569 plus a survivor q for the specified sieve. This is a subrange of the finite witness computation in Richstein's Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; a 10-million-block-index partition of Richstein2001.segmented_sieve_block_witnesses_chunk_7.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_7_part_5 (b : ℕ) (hb : b < 400000001)
    (hlo : 390000000 ≤ b) (hhi : b < 400000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry

end Richstein2001
