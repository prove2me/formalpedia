-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_3
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:41:36.446883+00:00
-- url     : https://prove2.me/theorems/1e001c84-a21f-4def-b03a-91794102b45b
-- title:
--   Segmented sieve witnesses, block subrange 270000000-279999999
-- statement:
--   For every block index b in [270000000,280000000), every even integer n in the corresponding million-integer block has a representation n = p + q, where p is a prime at most 5569 and q survives the specified sieve. This is a subrange of the finite witness computation for Richstein's Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived subrange of Richstein2001.segmented_sieve_block_witnesses_chunk_5.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_5_part_3 (b : Nat) (hb : Nat.lt b 400000001) (hlo : Nat.le 270000000 b) (hhi : Nat.lt b 280000000) :
    (forall n : Nat, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat => Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat => Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\ n = p + q))) := by sorry

end Richstein2001
