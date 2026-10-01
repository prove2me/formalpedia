-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_4_part_4
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_4_part_4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:19:45.262837+00:00
-- url     : https://prove2.me/theorems/64fe0887-bba6-46f1-bb0a-53fa064feaad
-- title:
--   Segmented sieve witnesses, block subrange 83000000-83999999
-- statement:
--   For every block index b in [83000000,84000000), every even n in its corresponding interval has a representation as a prime p at most 5569 plus a sieve survivor q in the specified range. This is a contiguous subrange of the finite witness computation of Richstein (2001).
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; contiguous block-range subgoal of the segmented sieve witness computation.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_4_part_4 (b : Nat) (hb : b < 400000001)
    (hlo : 83000000 <= b) (hhi : b < 84000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
