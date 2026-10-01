-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_5_sub_294
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_5_sub_294
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:20:49.899439+00:00
-- url     : https://prove2.me/theorems/3a7aa4e9-4871-4417-b79f-254ff31f43dd
-- title:
--   Segmented sieve witnesses, block subrange 294000000-294999999
-- statement:
--   For every block index b in [294000000,295000000), each even integer n in its million-integer interval is the sum of a prime p at most 5569 and a q that survives the specified sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; subrange of segmented_sieve_block_witnesses_chunk_5_part_5.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_5_part_5_sub_294 (b : Nat) (hb : Nat.lt b 400000001) (hlo : Nat.le 294000000 b) (hhi : Nat.lt b 295000000) :
    (forall n : Nat, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat => Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat => Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\ n = p + q))) := by sorry

end Richstein2001
