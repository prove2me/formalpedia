-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_2_upper
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_2_upper
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:20:58.60361+00:00
-- url     : https://prove2.me/theorems/4cd232a3-8730-4f17-819b-6169491c6938
-- title:
--   Segmented sieve witnesses, block range 65000000 to 69999999
-- statement:
--   For every block index b in [65000000 to 69999999], and every even integer n in its corresponding block, there are a prime p at most 5569 and a sieve survivor q in the specified range such that n = p + q. This is a subrange of the finite witness computation for Richstein's Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; contiguous block-range subgoal of the segmented sieve witness computation.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_1_range_2_upper
    (b : Nat) (hb : b < 400000001) (hlo : 65000000 <= b)
    (hhi : b < 70000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry

end Richstein2001
