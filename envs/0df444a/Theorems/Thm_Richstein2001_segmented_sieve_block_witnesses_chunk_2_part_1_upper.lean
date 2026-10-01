-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_2_part_1_upper
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_2_part_1_upper
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:04:13.749129+00:00
-- url     : https://prove2.me/theorems/999e96e9-3a73-4474-92c3-8988ab5fb43b
-- title:
--   Segmented sieve witnesses, second half of block range 100000000-109999999
-- statement:
--   For every block index b in [105000000,110000000), each even integer in its specified interval is a sum of a prime at most 5569 and a survivor of the specified sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; subdivision of the chunk 2 block-range subgoal.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_2_part_1_upper (b : Nat) (hb : b < 400000001) (hlo : Nat.le 105000000 b) (hhi : b < 110000000) : forall n, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n -> Exists fun p => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p) (Exists fun q => And (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q) (n = p + q)) := by sorry
end Richstein2001
