-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_interval_witness_chunk_2_part_3
-- name    : Richstein2001.segmented_sieve_interval_witness_chunk_2_part_3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:20:25.426743+00:00
-- url     : https://prove2.me/theorems/1468ea61-3f9c-41ea-9de8-170d90b90c4f
-- title:
--   Segmented sieve witnesses, interval 120000000000000 to 130000000000000
-- statement:
--   Every even integer n with 120000000000000 <= n < 130000000000000 is a sum p + q, where p is a prime in [2, 5569] and q is a survivor of the Goldbach sieve with the fixed interval parameters in the statement.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Mathematics of Computation 70 (2001), 1745-1749; fixed interval witness subgoal used by the chunk 2 block decomposition.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_interval_witness_chunk_2_part_3 (n : Nat)
    (hnlo : 120000000000000 <= n) (hnhi : n < 130000000000000)
    (hnEven : Even n) :
    Exists fun p => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
      (Exists fun q => And
        (Membership.mem (GoldbachSieve.survivors (120000000000000 - 5569)
          130000000000000 20000000) q) (n = p + q)) := by sorry
end Richstein2001
