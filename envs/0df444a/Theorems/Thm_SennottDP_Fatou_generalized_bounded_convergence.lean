-- Prove2me | Theorems.Thm_SennottDP_Fatou_generalized_bounded_convergence
-- name    : SennottDP.Fatou.generalized_bounded_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T12:34:21.672864+00:00
-- url     : https://prove2.me/theorems/0eb28a6a-ac57-467b-9d4f-021fc1444927
-- title:
--   Corollary A.2.7 — bounded convergence under approximating distributions
-- statement:
--   Assume hypotheses (i)–(iii) of Proposition A.2.5: $S$ is countable with a probability distribution $(P_j)$; $(S_N)$ is an increasing sequence of subsets with $\bigcup_N S_N = S$; $(P_j(N))_{j\in S_N}$ is a probability distribution on $S_N$ with $P_j(N)\to P_j$ for every $j$. Assume further:
--
--   4. $u(j,N)$ is a function of $j\in S_N$ and $N$ such that $\lim_{N\to\infty}u(j,N) = u(j)$ exists for every $j\in S$;
--   5. there is a finite constant $w$ with $|u(j,N)|\le w$ for all $N$ and $j\in S_N$.
--
--   Then $\lim_{N\to\infty}\sum_{j\in S_N} P_j(N)u(j,N)$ exists and
--   $$\lim_{N\to\infty}\ \sum_{j\in S_N} P_j(N)\, u(j,N) \;=\; \sum_{j\in S} P_j\, u(j).$$
--
--   This is the special case of Theorem A.2.6 in which the dominating function is a constant.
--
--   **Formalization Note** Hypotheses (i)–(iii) are `ApproxDist P SN Q`; $u$ is real valued, with its pointwise limit taken in `EReal`; the bound is required only on $S_N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 278, Corollary A.2.7

import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Corollary A.2.7, p. 278. (i)–(iii) of Proposition A.2.5 are
`ApproxDist P SN Q`; (iv) `u(j, N)` is a function of `j ∈ S_N` and `N` with `lim_N u(·, N) = u(·)`;
(v) there is a finite constant `w` with `|u| ≤ w`. Then `lim_N ∑_{j ∈ S_N} P_j(N) u(j, N)` exists and
equals `∑_{j ∈ S} P_j u(j)`. -/
theorem generalized_bounded_convergence {S : Type*} [Countable S] {P : S → ℝ≥0∞}
    {SN : ℕ → Set S} {Q : ℕ → S → ℝ≥0∞} (hA : ApproxDist P SN Q)
    (u : S → ℕ → ℝ) (uL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (w : ℝ) (hdom : ∀ N, ∀ j ∈ SN N, |u j N| ≤ w) :
    Tendsto (fun N => wsum ((SN N).indicator (Q N)) (fun j => (u j N : EReal))) atTop
      (𝓝 (wsum P uL)) := by sorry

end SennottDP.Fatou
