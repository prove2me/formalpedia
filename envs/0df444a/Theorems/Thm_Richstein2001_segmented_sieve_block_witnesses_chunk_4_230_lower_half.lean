-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_230_lower_half
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_4_230_lower_half
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:54:57.392933+00:00
-- url     : https://prove2.me/theorems/8be665cc-5ab5-4a0b-9eab-9f1a65f65b19
-- title:
--   Segmented sieve witnesses, lower half of block range 230000000-239999999
-- statement:
--   For each block index b in [230000000,235000000), every even integer in the corresponding block interval has a representation as a prime p no larger than 5569 plus a sieve survivor q in the specified interval.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; finite segmented sieve witness computation. block range 230000000-234999999.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_4_230_lower_half (b : Nat) (hb : b < 400000001) (hlo : 230000000 <= b) (hhi : b < 235000000) :
    forall n : Nat,
      Membership.mem ((Finset.Icc (max 4 (b * 1000000))
        (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      (Exists fun p : Nat => And
        (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
        (Exists fun q : Nat => And
          (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
            (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q)
          (n = p + q))) := by sorry
end Richstein2001
