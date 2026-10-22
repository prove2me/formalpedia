-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp10
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp10
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:36:18.381373+00:00
-- url     : https://prove2.me/theorems/7fee4361-875d-40e4-888d-5fceffbf879d
-- title:
--   Segmented sieve witnesses, blocks 50455500-50504999 (group 10 of 20 of part_1_upper)
-- statement:
--   For every block index $b$ with
--
--   $$
--   50455500\le b<50505000,
--   $$
--
--   every even integer $n$ with $\max(4,10^6 b)\le n\le\min(4\cdot10^{14},10^6(b+1)-1)$ can be written as $n=p+q$ with $p$ a prime, $2\le p\le 5569$, and $q$ a survivor of the sieve by the primes up to $2\cdot10^7$ on $[10^6 b-5569,\ \min(4\cdot10^{14},10^6(b+1)-1)]$ (`GoldbachSieve.survivors`).
--
--   Role: group $10$ of $20$ of `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper` (blocks $50010000$ to $50999999$); the groups tile that range end to end. Each group has width $49500$ in the block index $b$.
--
--   **Formalization Note** The conclusion matches the parent `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper` exactly; only the range of $b$ is restricted. This mirrors the already-proved decomposition of the sibling `..._part_1_lower` into twenty groups.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749, https://doi.org/10.1090/S0025-5718-00-01290-4, Section 2 (the segmented sieve: every even n in a block is p + q with p a small prime and q a sieve survivor); contiguous block-range subgoal of the parent `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper`.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp10 (b : Nat) (hb : b < 400000001)
    (hlo : 50455500 <= b) (hhi : b < 50505000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
