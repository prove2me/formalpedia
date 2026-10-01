-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_3_part_5_interval_witness
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_5_interval_witness
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:03:53.165187+00:00
-- url     : https://prove2.me/theorems/09ee4ea5-edbb-444a-9dee-3a1adab449ce
-- title:
--   Goldbach sieve witnesses on [190e12, 200e12)
-- statement:
--   For every even natural number n with 190000000000000 <= n < 200000000000000, there are a prime p <= 5569 and a natural number q such that n = p + q, and every prime r <= 20000000 dividing q is equal to q.
-- source:
--   Derived interval witness for Richstein2001.segmented_sieve_block_witnesses_chunk_3_part_5; J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_3_part_5_interval_witness
    (n : Nat) (hnlo : Nat.le 190000000000000 n)
    (hnhi : Nat.lt n 200000000000000) (heven : Even n) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.le p 5569) (And (Eq n (p + q))
        (forall r : Nat, Nat.Prime r -> Nat.le r 20000000 ->
          Dvd.dvd r q -> Eq r q))) := by sorry
end Richstein2001
