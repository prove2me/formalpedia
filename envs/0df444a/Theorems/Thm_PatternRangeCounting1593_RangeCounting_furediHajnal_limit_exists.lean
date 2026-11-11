-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_furediHajnal_limit_exists
-- name    : PatternRangeCounting1593.RangeCounting.furediHajnal_limit_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:40.755401+00:00
-- url     : https://prove2.me/theorems/37c994be-fe73-40c2-91f8-657b6b50dece
-- title:
--   Existence of the Füredi–Hajnal limit for patterns of length at least three
-- statement:
--   Let $\pi$ be a permutation pattern of length $k\ge 3$ and $\mathrm{ex}(n,\pi)$ the largest number of ones in an $n\times n$ 0-1 matrix avoiding the permutation matrix of $\pi$. Then the limit
--   $$c_\pi=\lim_{n\to\infty}\frac{\mathrm{ex}(n,\pi)}{n}$$
--   exists (and is finite).
--
--   The occupancy bound $\Delta=\lceil 10c_\pi\rceil$ of the Kozma–Opler hierarchy is defined from this limit; the paper calls it "the Füredi–Hajnal limit of $\pi$".
--
--   Differences from the source: none.
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §3.3, printed p. 11 (PDF p. 12), citing Füredi–Hajnal 1992 [FH92]; Marcus–Tardos 2004; Cibulka 2009; supporting theorem (not numbered in the paper)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
set_option autoImplicit false
open Filter Topology

namespace PatternRangeCounting1593.RangeCounting

/-- For a pattern of length at least three, `ex(n, π)/n` converges to the Füredi–Hajnal limit
`c_π` (Marcus–Tardos 2004 for finiteness; Cibulka 2009 for existence of the limit). -/
theorem furediHajnal_limit_exists {k : ℕ} (π : Equiv.Perm (Fin k)) (hk : 3 ≤ k) :
    Tendsto (fun n : ℕ => (exFH n π : ℝ) / n) atTop (𝓝 (fhLimit π)) := by sorry

end PatternRangeCounting1593.RangeCounting
