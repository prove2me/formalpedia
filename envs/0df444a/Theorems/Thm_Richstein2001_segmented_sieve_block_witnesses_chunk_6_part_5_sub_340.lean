-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_5_sub_340
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_5_sub_340
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:57:34.681522+00:00
-- url     : https://prove2.me/theorems/eed90fbd-ea6b-400b-8380-f98a6118aa19
-- title:
--   Segmented sieve witnesses, block range 340000000-340999999
-- statement:
--   For each block index b in [340000000,341000000), every even integer in the corresponding interval has a representation n = p + q, where p is a prime at most 5569 and q survives sieving by primes through 20,000,000 in the prescribed interval. This is a one-million-block subrange of Richstein's finite Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4 � 10^14, Math. Comp. 70 (2001), 1745-1749, DOI: 10.1090/S0025-5718-00-01290-4; computational block-range subgoal.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_6_part_5_sub_340 (b : Nat) (hb : b < 400000001)
    (hlo : LE.le 340000000 b) (hhi : b < 341000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
