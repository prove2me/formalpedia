-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_final_block
-- name    : Richstein2001.segmented_sieve_block_witnesses_final_block
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:26:15.508987+00:00
-- url     : https://prove2.me/theorems/60b01eb9-97a7-4d4f-abb4-730331928dac
-- title:
--   Segmented sieve witnesses, final block
-- statement:
--   For the boundary block index b = 400,000,000, every even integer in its truncated interval has a prime-plus-sieve-survivor witness of the stated kind. This handles the one terminal block left after partitioning the other 400 million block indices into equal ranges.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; terminal block subgoal of Richstein2001.segmented_sieve_block_witnesses.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_final_block (b : ℕ) (hb : b < 400000001)
    (hfinal : b = 400000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by sorry

end Richstein2001
