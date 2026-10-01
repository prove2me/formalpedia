-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_220_upper_half
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_4_220_upper_half
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:20:52.970635+00:00
-- url     : https://prove2.me/theorems/6279fdc0-236a-4a5f-8d8f-691cb11c01d5
-- title:
--   Segmented sieve witnesses, block 225000000-229999999
-- statement:
--   For every block index b in [225000000,230000000), every even integer in its interval has the prime-plus-sieve-survivor representation stated by the parent Richstein witness theorem.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; subdivision of the finite segmented sieve witness computation, block indices 225000000-229999999.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_4_220_upper_half (b : Nat)
    (hb : b < 400000001) (hlo : 225000000 <= b) (hhi : b < 230000000) :
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
