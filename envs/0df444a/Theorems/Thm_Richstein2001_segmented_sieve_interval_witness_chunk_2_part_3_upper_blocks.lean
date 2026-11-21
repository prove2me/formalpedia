-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_interval_witness_chunk_2_part_3_upper_blocks
-- name    : Richstein2001.segmented_sieve_interval_witness_chunk_2_part_3_upper_blocks
-- status  : Open
-- author  : @yuzhou
-- created : 2026-11-20T11:29:06.327579+00:00
-- url     : https://prove2.me/theorems/e55adc69-7dad-4937-9854-ca8c76eed425
-- title:
--   Richstein small-prime witnesses on [125000000000000, 130000000000000)
-- statement:
--   For each even integer $n$ in the half-open interval $[125000000000000,130000000000000)$, find a prime $p$ between 2 and 5569 and a summand $q$ such that $n=p+q$. Require $q$ to survive sieving by primes through 20,000,000 in the local interval $[125000000000000-5569,130000000000000]$, with sieving primes themselves retained.
-- source:
--   Localized interval from https://prove2.me/theorems/1468ea61-3f9c-41ea-9de8-170d90b90c4f.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

theorem Richstein2001.segmented_sieve_interval_witness_chunk_2_part_3_upper_blocks (n : Nat)
    (hnlo : 125000000000000 <= n) (hnhi : n < 130000000000000)
    (hnEven : Even n) :
    Exists fun p => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
      (Exists fun q => And
        (Membership.mem (GoldbachSieve.survivors (125000000000000 - 5569)
          130000000000000 20000000) q) (n = p + q)) := by sorry
