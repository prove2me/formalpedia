-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_eq_5_6
-- name    : TwoAgentSched.TotalTotal.eq_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:12.298654+00:00
-- url     : https://prove2.me/theorems/50d909c8-ed19-4ee2-b211-226e97bb0b35
-- title:
--   Proof of Theorem 9.2, Eqs. (5) and (6) — the two agents' total completion times in an SPT schedule
-- statement:
--   Let $p_1\le\dots\le p_k$ be nonnegative integers, $P=\sum_ip_i$, and consider an SPT schedule $\sigma$ of the instance of the proof of Theorem 9.2 (agents $A$ and $B$ each with jobs of lengths $p_1,\dots,p_k$; the pairs $J[1],\dots,J[k]$ in order). Let $x(0,p_h)=0$ if $A\prec_hB$ and $x(0,p_h)=p_h$ if $B\prec_hA$ in $\sigma$, and $x=\sum_{h=1}^kx(0,p_h)$. Then
--
--   $$\sum_{i=1}^kC^A_i(\sigma)=P+2\sum_{i=1}^k(k-i)p_i+x \qquad (5)$$
--
--   and
--
--   $$\sum_{i=1}^kC^B_i(\sigma)=P+2\sum_{i=1}^k(k-i)p_i+(P-x). \qquad (6)$$
--
--   So in an SPT schedule the split of $T$ between the two agents is governed by the single number $x$, the total length of the pairs in which $B$ goes first.
--
--   **Formalization Note** The SPT schedule is given by $x:\mathrm{Fin}\,k\to\mathrm{Bool}$ (`true` meaning $B\prec_hA$); $x$ of the paper is `xSum p x`. Indices are 0-based, so the weight $k-i$ is $k-(i+1)$.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 237, proof of Theorem 9.2, Eqs. (5) and (6)

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

namespace TwoAgentSched.TotalTotal

/-- Proof of Theorem 9.2, Eqs. (5) and (6) (Agnetis et al. 2004, p. 237): for integers
`p_1 ≤ ⋯ ≤ p_k` and the SPT schedule given by `x`, with `x = ∑_h x(0, p_h)` the total length of
the pairs in which B precedes A,
`∑ C^A_i = P + 2 ∑_{i=1}^k (k - i) p_i + x` (5) and
`∑ C^B_i = P + 2 ∑_{i=1}^k (k - i) p_i + (P - x)` (6). -/
theorem eq_5_6 {k : ℕ} (p : Fin k → ℕ) (hp : Monotone p) (x : Fin k → Bool) :
    (construction p).sumCA (sptSeq x) =
        (bigP p : ℝ) + 2 * (weightedSum p : ℝ) + (xSum p x : ℝ) ∧
      (construction p).sumCB (sptSeq x) =
        (bigP p : ℝ) + 2 * (weightedSum p : ℝ) + ((bigP p : ℝ) - (xSum p x : ℝ)) := by sorry

end TwoAgentSched.TotalTotal
