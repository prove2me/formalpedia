-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b8
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b8
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:10:12.652424+00:00
-- url     : https://prove2.me/theorems/ce5fbd37-08a3-49b8-9bc8-4cd229b3f14d
-- title:
--   Segmented sieve witnesses, block 50010018 only (grp01 c0002 block 8)
-- statement:
--   One-block slice for million-block $50010018$.
-- source:
--   J. Richstein, Math. Comp. 70 (2001), 1745-1749, Section 2; micro-chunk of upper_grp01.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0002_b8 (b : Nat) (hb : b < 400000001)
    (hlo : 50010018 <= b) (hhi : b < 50010019) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
