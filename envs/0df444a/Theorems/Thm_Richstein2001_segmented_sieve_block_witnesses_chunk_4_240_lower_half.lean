-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_4_240_lower_half
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_4_240_lower_half
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:53:58.767087+00:00
-- url     : https://prove2.me/theorems/0a7d12df-66e4-4437-82ad-d2919e6580cf
-- title:
--   Segmented sieve witnesses for 240000000 ? b < 245000000
-- statement:
--   For every block index b in [240000000,245000000), each even integer in its corresponding million-number block has a representation as a prime at most 5569 plus a survivor of the sieve by primes up to 20000000, as in Richstein's finite verification.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4�10^14, Mathematics of Computation 70 (2001), 1745-1749; partition of the stated segmented-sieve block range.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001
theorem segmented_sieve_block_witnesses_chunk_4_240_lower_half (b : Nat)
    (hb : b < 400000001) (hlo : 240000000 <= b) (hhi : b < 245000000) :
    forall n : Nat,
      Membership.mem ((Finset.Icc (max 4 (b * 1000000))
        (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      (Exists fun p : Nat => And
        (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
        (Exists fun q : Nat => And
          (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
            (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q)
          (n = p + q))) := by sorry
end Richstein2001
