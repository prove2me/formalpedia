-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_1_sub_5
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_1_sub_5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:01:55.316273+00:00
-- url     : https://prove2.me/theorems/cba12784-6275-4229-9d79-af4b0e25079a
-- title:
--   Segmented sieve witnesses, block 358000000-359999999
-- statement:
--   For every block index b in [358000000, 360000000), every even integer in its associated interval is a prime at most 5569 plus a survivor for the specified sieve.
-- source:
--   Subrange decomposition of Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_1.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_7_part_1_sub_5 (b : Nat) (hb : b < 400000001)
    (hlo : 358000000 <= b) (hhi : b < 360000000) :
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
