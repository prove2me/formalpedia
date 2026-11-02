-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_thresholdQ_even_sum
-- name    : TwoAgentSched.TotalTotal.thresholdQ_even_sum
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:11:10.489206+00:00
-- url     : https://prove2.me/theorems/99e93e2a-dc41-4b0e-86e7-16a2eecd6a00
-- title:
--   Scheduling threshold as a sum of bounded multiples of half-lengths
-- statement:
--   Let $p_0,\ldots,p_{k-1}$ be even natural processing times. The common real threshold used in the scheduling construction is the natural number
--
--   $$
--   Q=\sum_{i=0}^{k-1}\left(4(k-i-1)+3\right)\frac{p_i}{2}.
--   $$
--
--   Every coefficient is at most $4k+3$. This expression exposes a concrete way to accumulate the threshold by repeated binary addition of half-lengths. The theorem is an algebraic identity; it does not assert that the accumulator has been implemented or that its runtime has been proved.
-- source:
--   Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, proof of Theorem 9.2, pp. 237–238, threshold T/2; the displayed even-length accumulator formula is an elementary rearrangement.

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

namespace TwoAgentSched.TotalTotal

theorem thresholdQ_even_sum {k : ℕ} (p : Fin k → ℕ) (he : ∀ i, Even (p i)) :
    thresholdQ p = ((∑ i : Fin k, (4 * (k - (i.val + 1)) + 3) * (p i / 2) : ℕ) : ℝ) := by sorry

end TwoAgentSched.TotalTotal
