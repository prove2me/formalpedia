-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp10
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp10
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-10T03:02:59.192751+00:00
-- url     : https://prove2.me/theorems/cd84f791-47d3-411f-90cc-71fd4ad798d5
-- title:
--   Segmented sieve witnesses, blocks 50004500-50004999 (group 10 of 20)
-- statement:
--   For every block index $b$ with
--
--   $$
--   50004500\le b<50005000,
--   $$
--
--   every even integer $n$ with $\max(4,10^6 b)\le n\le\min(4\cdot10^{14},10^6(b+1)-1)$ can be written as $n=p+q$ with $p$ a prime, $2\le p\le 5569$, and $q$ a survivor of the sieve by the primes up to $2\cdot10^7$ on $[10^6 b-5569,\ \min(4\cdot10^{14},10^6(b+1)-1)]$ (`GoldbachSieve.survivors`).
--
--   Role: group 10 of 20 of `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower` (blocks 50000000 to 50009999); the groups tile that range end to end. The group spans exactly the chunks `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0451` through `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_c0500` (chunks 451 to 500 of 1000) and has the same form as the chunks.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749, https://doi.org/10.1090/S0025-5718-00-01290-4, Section 2 (the segmented sieve: every even n in a block is p + q with p a small prime and q a sieve survivor); contiguous block-range subgoal of the parent `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1`

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_lower_grp10 (b : Nat) (hb : b < 400000001)
    (hlo : 50004500 <= b) (hhi : b < 50005000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
