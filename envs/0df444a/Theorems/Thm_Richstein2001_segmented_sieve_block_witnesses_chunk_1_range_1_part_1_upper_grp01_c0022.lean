-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0022
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0022
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:56:14.554984+00:00
-- url     : https://prove2.me/theorems/7aace3ee-e0bb-5077-b4fd-4bc65ffbf7bf
-- title:
--   Richstein segmented sieve witnesses for blocks 50,010,210–50,010,219
-- statement:
--   For each block index $50{,}010{,}210 \le b < 50{,}010{,}220$, take an even integer $n$ between $10^6 b$ and $10^6(b+1)-1$, inclusive. Then $n=p+q$ for a prime $p \le 5569$ and a number $q$ that survives the sieve by all primes up to $20{,}000{,}000$ on $[10^6 b-5569,10^6(b+1)-1]$. Together the ten blocks contain 5,000,000 even integers.
-- source:
--   Jörg Richstein, Verifying the Goldbach conjecture up to 4·10^14, Math. Comp. 70 (2001), 1745–1749, section 2, https://doi.org/10.1090/S0025-5718-00-01290-4. Contiguous ten-block subrange of https://prove2.me/theorems/3d358a27-e70c-48b9-ba0c-f70eff97b522, following the adjacent range https://prove2.me/theorems/c6555507-a475-40ec-9927-c286477e257e.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_1_range_1_part_1_upper_grp01_c0022 (b : Nat) (hb : b < 400000001)
    (hlo : 50010210 <= b) (hhi : b < 50010220) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      exists (p : Nat), Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p /\
        exists (q : Nat), Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q /\
          n = p + q := by sorry
end Richstein2001
