-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_1
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:19:43.729244+00:00
-- url     : https://prove2.me/theorems/01c4c84d-6ebd-4d0e-9907-d1f509ff39b8
-- title:
--   Segmented sieve witnesses, block subrange 80000000-80999999
-- statement:
--   For every block index b in [80000000,81000000), every even n in its corresponding interval has a representation as a prime p at most 5569 plus a sieve survivor q in the specified range. This is a contiguous subrange of the finite witness computation of Richstein (2001).
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; contiguous block-range subgoal of the segmented sieve witness computation.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_4_part_1 (b : Nat) (hb : b < 400000001)
    (hlo : 80000000 <= b) (hhi : b < 81000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
