-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_200_part_4
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_4_200_part_4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:54:34.129906+00:00
-- url     : https://prove2.me/theorems/0f96c26d-cea5-416f-aabf-b1cf669eb602
-- title:
--   Segmented sieve witnesses, blocks 206000000-207999999
-- statement:
--   For each block index b in [206000000,208000000), every even integer in the corresponding Richstein interval is a prime p <= 5569 plus a survivor q of the sieve by primes up to 20,000,000.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; finite segmented sieve witness computation, block subrange 206000000-207999999.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_4_200_part_4 (b : Nat) (hb : b < 400000001)
    (hlo : 206000000 <= b) (hhi : b < 208000000) :
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
