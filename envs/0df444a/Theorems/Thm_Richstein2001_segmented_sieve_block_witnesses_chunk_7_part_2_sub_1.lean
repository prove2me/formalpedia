-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_2_sub_1
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_2_sub_1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:19:30.980274+00:00
-- url     : https://prove2.me/theorems/a58bb218-62ce-4f3d-9aed-4b65bebe7ba3
-- title:
--   Segmented sieve witnesses, block range 360000000-361999999
-- statement:
--   For every block index b in [360000000,361999999], each even integer in the corresponding Richstein segmented-sieve interval is the sum of a prime p at most 5569 and a number q surviving the specified sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; finite witness computation, subrange of chunk 7 part 2.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_7_part_2_sub_1 (b : Nat) (hb : b < 400000001)
    (hlo : 360000000 <= b) (hhi : b < 362000000) :
    forall n : Nat,
      Membership.mem ((Finset.Icc (max 4 (b * 1000000))
        (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists fun p : Nat => And
        (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
        (Exists fun q : Nat => And
          (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
            (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q)
          (n = p + q)) := by sorry

end Richstein2001
