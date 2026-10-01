-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_200
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_4_200
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:40:13.936473+00:00
-- url     : https://prove2.me/theorems/2f59e53d-facb-4cf9-8ba6-0d1f00edcf85
-- title:
--   Segmented sieve witnesses, block range 200000000-209999999
-- statement:
--   For each block index b in [200000000,210000000), every even integer in the corresponding block interval has a representation as a prime p no larger than 5569 plus a sieve survivor q in the specified interval.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; finite segmented sieve witness computation, block range 200000000-209999999.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_4_200 (b : Nat) (hb : b < 400000001)
    (hlo : 200000000 <= b) (hhi : b < 210000000) :
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
