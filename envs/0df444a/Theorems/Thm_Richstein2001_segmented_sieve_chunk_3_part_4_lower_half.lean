-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_chunk_3_part_4_lower_half
-- name    : Richstein2001.segmented_sieve_chunk_3_part_4_lower_half
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:04:44.469688+00:00
-- url     : https://prove2.me/theorems/9e027e5c-4831-47b5-8b4f-c5db42ba2552
-- title:
--   Segmented sieve witnesses, lower half of block 180000000-189999999
-- statement:
--   For each block index b with 180000000 <= b < 190000000, every even integer n in the lower half of the block, from max(4, b*1000000) through b*1000000 + 499999, is a sum p + q, where p is prime and at most 5569 and q is a survivor of the specified sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; block-range subgoal of the finite witness computation.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_chunk_3_part_4_lower_half
    (b : Nat) (hb : b < 400000001) (hlo : Nat.le 180000000 b) (hhi : b < 190000000) :
    forall n : Nat, Membership.mem (Finset.filter (fun n => Even n)
      (Finset.Icc (max 4 (b * 1000000)) (b * 1000000 + 499999))) n ->
      Exists fun p : Nat => Membership.mem (Finset.filter Nat.Prime (Finset.Icc 2 5569)) p /\
        Exists fun q : Nat => Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\ n = p + q := by sorry
end Richstein2001
