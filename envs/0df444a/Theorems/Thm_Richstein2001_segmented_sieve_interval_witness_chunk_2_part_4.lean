-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_interval_witness_chunk_2_part_4
-- name    : Richstein2001.segmented_sieve_interval_witness_chunk_2_part_4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:22:08.907332+00:00
-- url     : https://prove2.me/theorems/ba9004ec-1b87-4c04-833c-850331728b71
-- title:
--   Segmented sieve interval witnesses, chunk 2 part 4
-- statement:
--   For each even integer in the range 130000000000000 ≤ n < 140000000000000, there are a prime p ≤ 5569 and a sieve survivor q for which n = p + q.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; fixed-interval witness lemma for block range 130000000-139999999.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_interval_witness_chunk_2_part_4 (n : Nat)
    (hnlo : 130000000000000 ≤ n) (hnhi : n < 140000000000000)
    (hnEven : Even n) :
    ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
      ∃ q ∈ GoldbachSieve.survivors (130000000000000 - 5569)
        140000000000000 20000000, n = p + q := by sorry
end Richstein2001
