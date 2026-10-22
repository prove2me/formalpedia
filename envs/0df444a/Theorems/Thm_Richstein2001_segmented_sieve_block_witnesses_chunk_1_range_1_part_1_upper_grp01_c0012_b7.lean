-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0012_b7
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0012_b7
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:54:11.991287+00:00
-- url     : https://prove2.me/theorems/232c1095-2676-488a-9663-1de2a565893d
-- title:
--   block 50010117 (c0012_b7)
-- statement:
--   One-block $50010117$.
-- source:
--   J. Richstein, Math. Comp. 70 (2001); micro-chunk of upper_grp01.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0012_b7 (b : Nat) (hb : b < 400000001)
    (hlo : 50010117 <= b) (hhi : b < 50010118) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
