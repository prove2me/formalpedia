-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_2
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:07:10.932461+00:00
-- url     : https://prove2.me/theorems/b78ea671-abba-4edf-8310-789563be01d3
-- title:
--   Segmented sieve witnesses, block range 60000000-69999999
-- statement:
--   For every block index b in [60000000,70000000), and every even integer n in the corresponding interval, there are a prime p at most 5569 and a sieve survivor q in the specified range such that n = p + q. This is one contiguous subrange of the finite witness computation for Richstein's Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; contiguous block-range subgoal of the segmented sieve witness computation.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_1_range_2 (b : Nat) (hb : b < 400000001)
    (hlo : 60000000 <= b) (hhi : b < 70000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry

end Richstein2001
