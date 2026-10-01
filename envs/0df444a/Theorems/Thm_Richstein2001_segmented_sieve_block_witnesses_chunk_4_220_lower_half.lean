-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_220_lower_half
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_4_220_lower_half
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:20:45.376723+00:00
-- url     : https://prove2.me/theorems/9297f233-5212-48f0-808c-205971b16d9b
-- title:
--   Segmented sieve witnesses, block 220000000-224999999
-- statement:
--   For every block index b in [220000000,225000000), every even integer in its interval has the prime-plus-sieve-survivor representation stated by the parent Richstein witness theorem.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; subdivision of the finite segmented sieve witness computation, block indices 220000000-224999999.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_4_220_lower_half (b : Nat)
    (hb : b < 400000001) (hlo : 220000000 <= b) (hhi : b < 225000000) :
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
