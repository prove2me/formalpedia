-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_6_part_3_sub_3
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_6_part_3_sub_3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T22:22:23.994228+00:00
-- url     : https://prove2.me/theorems/f7a6c7b9-0c98-4157-9e92-da595776578d
-- title:
--   Segmented sieve witnesses, block range 324000000-325999999
-- statement:
--   For every block index b in [324000000,326000000), and every even integer n in its corresponding interval, there are a prime p at most 5569 and a sieve survivor q in the specified range such that n = p + q. This is a subrange of Richstein's finite Goldbach verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; computational block-range subgoal.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_6_part_3_sub_3 (b : Nat) (hb : b < 400000001)
    (hlo : 324000000 ≤ b) (hhi : b < 326000000) :
    ∀ (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n →
      ∃ (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p ∧
        ∃ (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q ∧
          n = p + q := by sorry
end Richstein2001
