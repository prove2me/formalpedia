-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_2
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:41:26.000373+00:00
-- url     : https://prove2.me/theorems/e20bb02e-e793-4872-acb8-8817846ffaaf
-- title:
--   Segmented sieve witnesses, block range 110000000-119999999
-- statement:
--   For every block index b in [110000000,120000000), every even integer in that block's specified interval is a sum of a prime at most 5569 and a survivor of the specified sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; subdivision of the chunk 2 block-range subgoal.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_2_part_2 (b : Nat) (hb : b < 400000001) (hlo : 110000000 <= b) (hhi : b < 120000000) : forall n, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n -> Exists fun p => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p) (Exists fun q => And (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q) (n = p + q)) := by sorry
end Richstein2001
