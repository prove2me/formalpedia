-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_5_part_3_sub_2
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_5_part_3_sub_2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:56:53.159984+00:00
-- url     : https://prove2.me/theorems/70759846-6072-448e-8c64-ee4d5c6a0dd8
-- title:
--   Segmented sieve witnesses, subrange 272000000-273999999
-- statement:
--   For every block index b in [272000000,274000000), every even integer in the corresponding million-integer block is the sum of a prime p at most 5569 and a number q that survives the specified sieve.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; a subrange of the submitted block-witnesses theorem.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_5_part_3_sub_2 (b : Nat) (hb : Nat.lt b 400000001) (hlo : Nat.le 272000000 b) (hhi : Nat.lt b 274000000) :
    (forall n : Nat, Membership.mem ((Finset.Icc (max 4 (b * 1000000)) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun p : Nat => Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        Exists (fun q : Nat => Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569) (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\ n = p + q))) := by sorry

end Richstein2001
