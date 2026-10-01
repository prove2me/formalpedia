-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_block_witnesses_chunk_0_lower_half
-- name    : Richstein2001.segmented_sieve_block_witnesses_chunk_0_lower_half
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T21:44:57.162011+00:00
-- url     : https://prove2.me/theorems/fc44db04-962e-4873-9d23-36dd2c14523f
-- title:
--   Segmented sieve witnesses, lower half of block range 0
-- statement:
--   For each block index b from 0 through 24,999,999, every even n in the corresponding interval has a witness p and sieve survivor q.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4e14 (2001), range subdivision of Richstein2001.segmented_sieve_block_witnesses_chunk_0.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

theorem segmented_sieve_block_witnesses_chunk_0_lower_half (b : Nat)
    (hb : b < 400000001) (hlo : LE.le 0 b) (hhi : b < 25000000) :
    forall (n : Nat), Membership.mem ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) n ->
      Exists (fun (p : Nat) => And (Membership.mem ((Finset.Icc 2 5569).filter Nat.Prime) p)
        (Exists (fun (q : Nat) => And (Membership.mem (GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000) q)
          (n = p + q)))) := by sorry

end Richstein2001
