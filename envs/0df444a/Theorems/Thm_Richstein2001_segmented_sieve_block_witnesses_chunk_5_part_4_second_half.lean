-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_4_second_half
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_4_second_half
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:52:57.994876+00:00
-- url     : https://prove2.me/theorems/3e51e12b-c31b-4b1f-81d9-87b5809990fb
-- title:
--   Segmented sieve witnesses, subrange 285000000-289999999
-- statement:
--   Every even integer in each sieve block indexed by 285000000 ? b < 290000000 has a representation as a prime p ? 5569 plus a number surviving the stated sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_5_part_4_second_half (b : Nat) (hb : Nat.lt b 400000001) (hlo : Nat.le 285000000 b) (hhi : Nat.lt b 290000000) :
    (forall n : Nat, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat => Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat => Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\ n = p + q))) := by sorry

end Richstein2001
