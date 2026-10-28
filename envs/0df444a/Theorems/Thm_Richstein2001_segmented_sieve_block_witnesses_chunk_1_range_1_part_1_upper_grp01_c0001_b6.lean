-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001_b6
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001_b6
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:01:58.613887+00:00
-- url     : https://prove2.me/theorems/b8cf4c7e-ce12-45e7-ae73-77bca5d4fbd3
-- title:
--   Segmented sieve witnesses, block 50010006 only (grp01 c0001 block 6)
-- statement:
--   One-block slice: every even $n$ in the million-block indexed by $50010006$ is $p+q$ with $p$ prime $\le 5569$ and $q$ a GoldbachSieve survivor (cutoff $2\cdot 10^7$). Child of upper_grp01_c0001.
-- source:
--   J. Richstein, Math. Comp. 70 (2001), 1745-1749, Section 2; one-block slice of upper_grp01_c0001.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001_b6 (b : Nat) (hb : b < 400000001)
    (hlo : 50010006 <= b) (hhi : b < 50010007) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
