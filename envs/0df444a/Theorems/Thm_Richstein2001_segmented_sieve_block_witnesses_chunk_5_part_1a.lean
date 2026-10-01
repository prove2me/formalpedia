-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_1a
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_1a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:56:09.660329+00:00
-- url     : https://prove2.me/theorems/f36bde8b-d474-45c0-88a6-a0914d8e4111
-- title:
--   Segmented sieve witnesses, blocks 250000000-254999999
-- statement:
--   For every block index b in [250000000,255000000), each even integer in its million-integer interval is the sum of a prime at most 5569 and a number surviving the specified sieve. This is a subrange of Richstein's finite Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived subrange of segmented_sieve_block_witnesses_chunk_5_part_1.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_5_part_1a (b : Nat) (hb : Nat.lt b 400000001) (hlo : Nat.le 250000000 b) (hmid : Nat.lt b 255000000) :
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
