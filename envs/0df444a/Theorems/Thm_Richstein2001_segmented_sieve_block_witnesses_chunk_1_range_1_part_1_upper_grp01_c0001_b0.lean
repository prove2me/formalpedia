-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001_b0
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001_b0
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:56:56.660984+00:00
-- url     : https://prove2.me/theorems/b5c93d0d-d037-436a-8dbb-5e9f0159cdf9
-- title:
--   Segmented sieve witnesses, block 50010000 only (grp01 c0001 first block)
-- statement:
--   For the single block index $b=50010000$, every even integer $n$ in that block's million-integer window can be written as $n=p+q$ with $p\le 5569$ prime and $q$ a `GoldbachSieve.survivors` witness at cutoff $2\cdot10^7$.
--
--   Role: first one-block slice of micro-chunk `..._grp01_c0001` (blocks $50010000$–$50010009$), sized so a packed Pocklington/RSFrame certificate fits in a single Lean verification job.
-- source:
--   J. Richstein, Math. Comp. 70 (2001), 1745-1749, Section 2; one-block slice of Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001_b0 (b : Nat) (hb : b < 400000001)
    (hlo : 50010000 <= b) (hhi : b < 50010001) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
