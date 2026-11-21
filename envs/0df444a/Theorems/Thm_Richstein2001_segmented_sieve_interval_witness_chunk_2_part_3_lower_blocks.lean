-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_interval_witness_chunk_2_part_3_lower_blocks
-- name    : Richstein2001.segmented_sieve_interval_witness_chunk_2_part_3_lower_blocks
-- status  : Open
-- author  : @yuzhou
-- created : 2026-11-20T11:29:07.164643+00:00
-- url     : https://prove2.me/theorems/878703c6-2018-4011-b0d1-e5b5390f5ca0
-- title:
--   Richstein small-prime witnesses on [120000000000016, 125000000000000)
-- statement:
--   For each even integer $n$ in the half-open interval $[120000000000016,125000000000000)$, find a prime $p$ between 2 and 5569 and a summand $q$ such that $n=p+q$. Require $q$ to survive sieving by primes through 20,000,000 in the local interval $[120000000000016-5569,125000000000000]$, with sieving primes themselves retained.
-- source:
--   Localized interval from https://prove2.me/theorems/1468ea61-3f9c-41ea-9de8-170d90b90c4f.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

theorem Richstein2001.segmented_sieve_interval_witness_chunk_2_part_3_lower_blocks (n : Nat)
    (hnlo : 120000000000016 <= n) (hnhi : n < 125000000000000)
    (hnEven : Even n) :
    Exists fun p => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
      (Exists fun q => And
        (Membership.mem (GoldbachSieve.survivors (120000000000016 - 5569)
          125000000000000 20000000) q) (n = p + q)) := by sorry
