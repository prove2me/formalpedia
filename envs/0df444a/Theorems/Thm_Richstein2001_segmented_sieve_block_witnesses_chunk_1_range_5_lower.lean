-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_5_lower
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_5_lower
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:24:49.569386+00:00
-- url     : https://prove2.me/theorems/06b8f463-f87d-426e-bd5f-282727a22ac4
-- title:
--   Segmented sieve witnesses, block range 90000000-94999999
-- statement:
--   For every block index b in [90000000,95000000), and every even integer n in its corresponding interval, there are a prime p at most 5569 and a sieve survivor q in the prescribed interval such that n = p + q. This is one half of the final contiguous block range in Richstein's finite Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; contiguous block-range subgoal of the segmented sieve witness computation.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_5_lower (b : Nat) (hb : b < 400000001)
    (hlo : 90000000 <= b) (hhi : b < 95000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q:= by sorry
end Richstein2001
