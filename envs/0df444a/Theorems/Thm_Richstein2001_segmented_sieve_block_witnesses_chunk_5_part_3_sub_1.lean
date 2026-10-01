-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_3_sub_1
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_3_sub_1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:56:51.527533+00:00
-- url     : https://prove2.me/theorems/ec698b1d-aae1-4eb1-a711-7168ea41fb97
-- title:
--   Segmented sieve witnesses, subrange 270000000-271999999
-- statement:
--   For every block index b in [270000000,272000000), every even integer in the corresponding million-integer block is the sum of a prime p at most 5569 and a number q that survives the specified sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; a subrange of the submitted block-witnesses theorem.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_5_part_3_sub_1 (b : Nat) (hb : Nat.lt b 400000001) (hlo : Nat.le 270000000 b) (hhi : Nat.lt b 272000000) :
    (forall n : Nat, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat => Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat => Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\ n = p + q))) := by sorry

end Richstein2001
