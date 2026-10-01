-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0_upper_half_part_4
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_0_upper_half_part_4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:52:33.842788+00:00
-- url     : https://prove2.me/theorems/e51ac2d8-b1d5-473f-9a81-ce65166fb1e8
-- title:
--   Segmented sieve witnesses, upper half block 0 subrange 40000000-44999999
-- statement:
--   For every block index b in [40000000,45000000), and every even integer n in its corresponding interval, there are a prime p at most 5569 and a sieve survivor q in the specified range such that n = p + q.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749; derived subdivision of Richstein2001.segmented_sieve_block_witnesses_chunk_0_upper_half.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_0_upper_half_part_4 (b : Nat)
    (hb : b < 400000001) (hlo : LE.le 0 b)
    (hloRange : LE.le 40000000 b) (hhi : b < 45000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun (p : Nat) => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
        (Exists (fun (q : Nat) => And (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q)
          (n = p + q)))) := by sorry

end Richstein2001
