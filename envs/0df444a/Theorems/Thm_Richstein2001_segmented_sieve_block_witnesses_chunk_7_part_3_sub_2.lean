-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_7_part_3_sub_2
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_3_sub_2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:05:26.336523+00:00
-- url     : https://prove2.me/theorems/003fe08e-b8d1-49ea-844c-ce3501586e22
-- title:
--   Segmented sieve witnesses, block range 372000000-373999999
-- statement:
--   For each block index b in [372000000,374000000), every even integer in the associated interval has a representation as a prime p at most 5569 plus a survivor q for the specified sieve.
-- source:
--   A two-million-block-index subrange of the finite witness computation in Richstein2001.segmented_sieve_block_witnesses_chunk_7_part_3.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_7_part_3_sub_2 (b : Nat) (hb : b < 400000001)
    (hlo : LE.le 372000000 b) (hhi : b < 374000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry

end Richstein2001
