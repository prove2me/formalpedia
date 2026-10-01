-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_1_lower
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_1_lower
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:04:11.646807+00:00
-- url     : https://prove2.me/theorems/9a1a1531-6287-4e26-9ee5-dfeb6fd6279a
-- title:
--   Segmented sieve witnesses, first half of block range 100000000-109999999
-- statement:
--   For every block index b in [100000000,105000000), each even integer in its specified interval is a sum of a prime at most 5569 and a survivor of the specified sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; subdivision of the chunk 2 block-range subgoal.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_2_part_1_lower (b : Nat) (hb : b < 400000001) (hlo : Nat.le 100000000 b) (hhi : b < 105000000) : forall n, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n -> Exists fun p => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p) (Exists fun q => And (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q) (n = p + q)) := by sorry
end Richstein2001
