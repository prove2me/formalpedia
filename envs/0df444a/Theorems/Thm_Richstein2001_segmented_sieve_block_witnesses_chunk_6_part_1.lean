-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_1
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:41:58.917647+00:00
-- url     : https://prove2.me/theorems/d3973310-2206-4873-aac5-c29ddf79bd8a
-- title:
--   Segmented sieve witnesses, block range 300000000-309999999
-- statement:
--   For every block index b in [300000000,310000000), and every even integer n in its corresponding interval, there are a prime p at most 5569 and a sieve survivor q in the specified range such that n = p + q. This is a ten-million-block segment of Richstein's finite Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; computational block-range subgoal of Richstein2001.segmented_sieve_block_witnesses.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_6_part_1 (b : Nat) (hb : b < 400000001)
    (hlo : LE.le 300000000 b) (hhi : b < 310000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry

end Richstein2001
