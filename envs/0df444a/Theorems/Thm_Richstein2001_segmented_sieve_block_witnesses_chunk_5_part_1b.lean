-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_1b
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_1b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:56:13.222363+00:00
-- url     : https://prove2.me/theorems/bd330a26-1164-4723-8b19-843eff29b49b
-- title:
--   Segmented sieve witnesses, blocks 255000000-259999999
-- statement:
--   For every block index b in [255000000,260000000), each even integer in its million-integer interval is the sum of a prime at most 5569 and a number surviving the specified sieve. This is a subrange of Richstein's finite Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived subrange of segmented_sieve_block_witnesses_chunk_5_part_1.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_5_part_1b (b : Nat) (hb : Nat.lt b 400000001) (hmid : Nat.le 255000000 b) (hhi : Nat.lt b 260000000) :
    (forall n : Nat,
      Membership.mem ((Finset.Icc (max 4 (b * 1000000))
        (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat =>
        Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat =>
          Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
            (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q))) := by sorry
end Richstein2001
