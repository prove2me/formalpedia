-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0004
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0004
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:19:54.853713+00:00
-- url     : https://prove2.me/theorems/82bebfba-9b57-4151-99c3-6cfbb7eba09d
-- title:
--   Segmented sieve witnesses, blocks 50010030-50010039 (grp01 micro-chunk 4)
-- statement:
--   Million-blocks $50010030$–$50010039$.
-- source:
--   J. Richstein, Math. Comp. 70 (2001); micro-chunk of upper_grp01.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0004 (b : Nat) (hb : b < 400000001)
    (hlo : 50010030 <= b) (hhi : b < 50010040) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
