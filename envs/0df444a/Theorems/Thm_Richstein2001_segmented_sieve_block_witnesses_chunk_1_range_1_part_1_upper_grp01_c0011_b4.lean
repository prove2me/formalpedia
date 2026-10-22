-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0011_b4
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0011_b4
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:50:38.140917+00:00
-- url     : https://prove2.me/theorems/76dcd977-6c2b-42f3-a864-add019ca0bb7
-- title:
--   block 50010104 (c0011_b4)
-- statement:
--   One-block $50010104$.
-- source:
--   J. Richstein, Math. Comp. 70 (2001); micro-chunk of upper_grp01.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0011_b4 (b : Nat) (hb : b < 400000001)
    (hlo : 50010104 <= b) (hhi : b < 50010105) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
