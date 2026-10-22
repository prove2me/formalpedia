-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0003
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0003
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:17:07.574921+00:00
-- url     : https://prove2.me/theorems/cbfcf0ca-98ad-4673-9e9c-31c703abae77
-- title:
--   Segmented sieve witnesses, blocks 50010020-50010029 (grp01 micro-chunk 3)
-- statement:
--   Million-blocks $50010020$–$50010029$: even $n=p+q$ with $p\le 5569$ prime and $q$ GoldbachSieve survivor.
-- source:
--   J. Richstein, Math. Comp. 70 (2001); micro-chunk of upper_grp01.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0003 (b : Nat) (hb : b < 400000001)
    (hlo : 50010020 <= b) (hhi : b < 50010030) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
