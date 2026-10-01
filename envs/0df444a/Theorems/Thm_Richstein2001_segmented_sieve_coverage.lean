-- Prove2me | Theorems.Thm_Richstein2001_segmented_sieve_coverage
-- name    : Richstein2001.segmented_sieve_coverage
-- status  : Open
-- author  : @webmh
-- created : 2026-09-11T23:28:01.077105+00:00
-- url     : https://prove2.me/theorems/73281223-e520-4706-9186-a986548dc0d1
-- title:
--   Finite sieve coverage of the Richstein range in blocks of one million
-- statement:
--   Let $N=4\cdot10^{14}$, $B=10^6$, $P=5569$, $R=20{,}000{,}000$, and let $S(L,U,R)$ be the finite survivor set defined in `GoldbachSieve`: numbers at least 2 in $[L,U]$ with no prime divisor at most $R$ other than themselves.
--
--   For every integer $0\le b<400{,}000{,}001$, put $L_b=bB$ and $U_b=\min(N,(b+1)B-1)$. The finite coverage assertion is
--
--   $$\{n\in[\max(4,L_b),U_b]:2\mid n\}\subseteq
--   \bigcup_{p\le5569,\ p\text{ prime}}(p+S(\max(0,L_b-5569),U_b,R)).$$
--
--   This is the outstanding computational obligation in a sieve-based formalization of Richstein's verification. The original abstract reports the range and maximal smaller prime 5569. The block width and certificate interface are formalization choices. No certificate data or Lean verification of all these blocks is supplied with this statement. The last block includes the endpoint $N$; the first block includes $4=2+2$.
-- source:
--   J. Richstein, Verifying the Goldbach conjecture up to 4·10^14, Math. Comp. 70 (2001), 1745–1749; abstract p. 1745 reports segmented sieving and maximal smaller prime 5569. https://doi.org/10.1090/S0025-5718-00-01290-4 . The finite-set interface and width 10^6 are this formalization's choices, not a transcription of the original program or recovered certificates.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace Richstein2001

/-- Finite segmented sieve coverage obligation; the computational data remain open. -/
theorem segmented_sieve_coverage (b : ℕ) (hb : b < 400000001) :
    ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)) ⊆
    GoldbachSieve.pairSums 5569 (b * 1000000 - 5569)
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000 := by sorry

end Richstein2001
