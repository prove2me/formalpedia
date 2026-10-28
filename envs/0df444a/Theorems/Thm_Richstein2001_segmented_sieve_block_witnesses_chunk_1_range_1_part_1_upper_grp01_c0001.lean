-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:40:52.379203+00:00
-- url     : https://prove2.me/theorems/cc44a0e6-120e-4a22-aad4-408177475510
-- title:
--   Segmented sieve witnesses, blocks 50010000-50010009 (grp01 micro-chunk 1)
-- statement:
--   For every block index $b$ with
--
--   $$
--   50010000\le b<50010010,
--   $$
--
--   every even integer $n$ with $\max(4,10^6 b)\le n\le\min(4\cdot10^{14},10^6(b+1)-1)$ can be written as $n=p+q$ with $p$ a prime, $2\le p\le 5569$, and $q$ a survivor of the sieve by the primes up to $2\cdot10^7$ on $[10^6 b-5569,\ \min(4\cdot10^{14},10^6(b+1)-1)]$ (`GoldbachSieve.survivors`).
--
--   Role: micro-chunk 1 of `Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01` (blocks 50010000 to 50059499); each micro-chunk covers 10 consecutive block indices, matching the proved `..._part_1_lower_c0001` pattern.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14, Math. Comp. 70 (2001), 1745-1749, https://doi.org/10.1090/S0025-5718-00-01290-4, Section 2; 10-block micro-chunk of Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0001 (b : Nat) (hb : b < 400000001)
    (hlo : 50010000 <= b) (hhi : b < 50010010) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
