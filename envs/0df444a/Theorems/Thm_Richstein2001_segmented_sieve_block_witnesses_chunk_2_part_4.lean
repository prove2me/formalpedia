-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_4
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:41:25.813755+00:00
-- url     : https://prove2.me/theorems/7b6a182a-3264-4c28-accb-2a5ca38eff3d
-- title:
--   Segmented sieve witnesses, block range 130000000-139999999
-- statement:
--   For every block index b in [130000000,140000000), every even integer in that block's specified interval is a sum of a prime at most 5569 and a survivor of the specified sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; subdivision of the chunk 2 block-range subgoal.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_2_part_4 (b : Nat) (hb : b < 400000001) (hlo : 130000000 <= b) (hhi : b < 140000000) : forall n, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n -> Exists fun p => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p) (Exists fun q => And (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q) (n = p + q)) := by sorry
end Richstein2001
