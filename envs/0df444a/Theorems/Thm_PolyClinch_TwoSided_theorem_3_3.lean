-- Prove2me | Theorems.Thm_PolyClinch_TwoSided_theorem_3_3
-- name    : PolyClinch.TwoSided.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:00.843394+00:00
-- url     : https://prove2.me/theorems/86f682ce-b260-46e2-827b-84dfcb509af0
-- title:
--   Theorem 3.3, p. 10 — Algorithm 1 satisfies (ICb) and (IRb), and its final y lies in the base polytope of P̃
-- statement:
--   Let $\mathcal I$ be valid public information (bids and reserve prices multiples of $\varepsilon>0$, nonnegative budgets, monotone submodular $f_j$), and consider its reduced one-sided market: buyers $N$ (the $n$ real and $m$ virtual buyers), feasible set $\tilde P$, budgets $B$ with $B_{n+j}=\infty$, and bids $v'$ (with $v'_{n+j}=\rho_j$). Fix a buyer $i\in N$ and a true value $t\in\varepsilon\mathbb N$. Let $(y,\pi)$ be any output of Algorithm 1 at the bids $v'$, and $(y',\pi')$ any output when buyer $i$'s bid is replaced by $t$. With
--   $$
--   u_i(y,\pi)=\begin{cases} t\,y_i-\pi_i & \pi_i\le B_i,\\ -\infty&\text{otherwise,}\end{cases}
--   $$
--   we have
--   $$
--   u_i(y,\pi)\le u_i(y',\pi'),\qquad u_i(y',\pi')\ge 0,
--   $$
--   and $y$ belongs to the base polytope of $\tilde P$, i.e. $y\in\tilde P$ and $y(N)\ge z(N)$ for every $z\in\tilde P$.
--
--   This is the theorem of Goel et al. on the polyhedral clinching auction, applied to the reduced market; it is what carries incentive compatibility over to Mechanism 2 (Corollary 3.10).
--
--   **Formalization Note** Outputs are terminal states of runs of the relation `Alg1Outcome`. The deviating bid $t$ is on the $\varepsilon$-grid (Assumption 3.2). The base polytope is expressed as "maximum coordinate sum over $\tilde P$", which equals $\{y\in\tilde P\mid y(N)=g(N)\}$ for the rank function $g$ of the polymatroid $\tilde P$.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 10, Theorem 3.3 (Goel et al. [14])

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Clinching

namespace PolyClinch.TwoSided

/-- Theorem 3.3 (Goel et al.; Hirai–Sato p. 10). Algorithm 1 on the reduced one-sided market of a
valid input `I` (buyers `Fin (n + m)`, feasible set `P̃`, budgets `B` with `B_{n+j} = ∞`, bids
`v′` and `ρ`) satisfies (ICb) and (IRb) for every buyer `i` and every true value `t` on the
`ε`-grid, and its final transaction vector lies in the base polytope of `P̃`. -/
theorem theorem_3_3 {n m : ℕ} (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε)
    (I : PublicInfo E) (hI : Valid E ε I) (i : Fin (n + m)) (t : ℝ) (ht : OnGrid ε t)
    (S S' : Alg1State (n + m))
    (hS : Alg1Outcome (reducedP E I) (extBudget E I) (extBid E I) ε S)
    (hS' : Alg1Outcome (reducedP E I) (extBudget E I) (Function.update (extBid E I) i t) ε S') :
    oneSidedUtility (extBudget E I) t S i ≤ oneSidedUtility (extBudget E I) t S' i ∧
      0 ≤ oneSidedUtility (extBudget E I) t S' i ∧
      IsMaxSumPoint (reducedP E I) S.y := by sorry

end PolyClinch.TwoSided
