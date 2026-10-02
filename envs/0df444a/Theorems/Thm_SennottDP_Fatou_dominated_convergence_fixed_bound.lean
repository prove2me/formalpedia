-- Prove2me | Theorems.Thm_SennottDP_Fatou_dominated_convergence_fixed_bound
-- name    : SennottDP.Fatou.dominated_convergence_fixed_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T12:23:19.071972+00:00
-- url     : https://prove2.me/theorems/6f8b9e13-c34e-4758-a0e4-b921e5edb133
-- title:
--   Corollary A.2.4 — dominated convergence with a dominating function independent of N
-- statement:
--   Assume:
--
--   1. $S$ is a countable set with a probability distribution $(P_j)_{j\in S}$;
--   2. $u(j,N)$ is a function of $j\in S$ and $N$ such that $\lim_{N\to\infty}u(j,N) = u(j)$ exists for every $j$;
--   3. $w$ is a finite function on $S$ with $|u(j,N)|\le w(j)$ for all $j, N$ and $\sum_{j\in S} P_j\, w(j) < \infty$.
--
--   Then $\lim_{N\to\infty}\sum_{j\in S} P_j u(j,N)$ exists and
--   $$\lim_{N\to\infty}\ \sum_{j\in S} P_j\, u(j,N) \;=\; \sum_{j\in S} P_j\, u(j).$$
--
--   This is the special case of Theorem A.2.3 in which the dominating function does not depend on $N$; it is the form most often applied to expected costs.
--
--   **Formalization Note** $u$ is real valued (it is bounded by the finite function $w$); its pointwise limit is taken in `EReal`. Sums are the weighted sum `wsum`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 277, Corollary A.2.4

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Corollary A.2.4, p. 277. (i) `S` is countable with probability distribution
`(P_j)`; (ii) `lim_N u(·, N) = u(·)` exists; (iii) `w` is a finite function on `S` with `|u| ≤ w`
and `∑_j P_j w(j) < ∞`. Then `lim_N ∑_j P_j u(j, N)` exists and equals `∑_j P_j u(j)`. -/
theorem dominated_convergence_fixed_bound {S : Type*} [Countable S] (P : S → ℝ≥0∞)
    (hP : ∑' j, P j = 1) (u : S → ℕ → ℝ) (uL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (w : S → ℝ) (hdom : ∀ j N, |u j N| ≤ w j) (hfin : wsum P (fun j => (w j : EReal)) < ⊤) :
    Tendsto (fun N => wsum P (fun j => (u j N : EReal))) atTop (𝓝 (wsum P uL)) := by sorry

end SennottDP.Fatou
