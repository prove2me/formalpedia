-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_proposition_4
-- name    : Sennott1989.AvgCost.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:42.32987+00:00
-- url     : https://prove2.me/theorems/b6d1c1c8-6f6b-4bea-b9e3-f25c3f15669d
-- title:
--   Proposition 4 (p. 629) — for an irreducible ergodic chain: Σ π_i c(i) < ∞ ⇔ all c_i0 < ∞ ⇔ a drift condition with a test function r
-- statement:
--   Let $(X_n)$ be an irreducible ergodic Markov chain on $0,1,2,\dots$ with transition probabilities $P_{ij}$ and steady state distribution $(\pi_i)$. In state $i$ a nonnegative cost $c(i)$ is incurred; let $c_{i0}$ (resp. $m_{i0}$) be the expected cost (resp. time) of a first passage from $i$ to $0$. The following are equivalent:
--
--   1. $\sum_i\pi_ic(i)<\infty$;
--   2. $c_{i0}<\infty$ for every $i$;
--   3. there exist a nonnegative integer $N$ and a nonnegative function $r$ such that
--   $$\sum_jP_{ij}r(j)<\infty\quad(0\le i\le N),\qquad \sum_jP_{ij}r(j)-r(i)\le-c(i)\quad(i>N).$$
--
--   Condition 3 is a practical test for the finiteness of the mean cost of a first passage to $0$.
--
--   **Formalization Note** "Ergodic" means every state positive recurrent (no aperiodicity). $\pi_i=1/m_{ii}$; $c_{00}$ is the expected cost of a return to $0$. Costs and $r$ are finite nonnegative reals; since $r(i)$ is finite, the drift inequality is written $\sum_jP_{ij}r(j)+c(i)\le r(i)$ in $[0,\infty]$.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, §2, Proposition 4, p. 629

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

/-- Sennott (1989), §2, Proposition 4, p. 629. Let `(X_n)` be an irreducible ergodic Markov chain
on `0, 1, 2, …` with transition probabilities `P_{ij}` and steady state distribution `(π_i)`. In
state `i` a nonnegative cost `c(i)` is incurred; `c_{i0}` (resp. `m_{i0}`) is the expected cost
(resp. time) of a first passage from `i` to `0`. The following are equivalent:

(i) `∑_i π_i c(i) < ∞`;
(ii) for every `i`, `c_{i0} < ∞`;
(iii) there exist a nonnegative integer `N` and a nonnegative function `r` with
`∑_j P_{ij} r(j) < ∞` for `0 ≤ i ≤ N` and `∑_j P_{ij} r(j) − r(i) ≤ −c(i)` for `i > N`.

**Formalization Note** "Ergodic" is positive recurrence of every state (`IrredErgodic`); `π_i` is
`SennottDP.MarkovCost.steadyState`, `c_{i0}` is `SennottDP.MarkovCost.passageCost` to `{0}`
(for `i = 0` the cost of a return to `0`, a passage of length `≥ 1`). Costs and `r` are finite and
nonnegative (`ℝ≥0`); all sums are in `[0, ∞]`. -/
theorem proposition_4 (Γ : SennottDP.MarkovCost.MC ℕ) (hΓ : IrredErgodic Γ) (c : ℕ → ℝ≥0) :
    List.TFAE [CostCondI Γ c, CostCondII Γ c, CostCondIII Γ c] := by sorry

end Sennott1989.AvgCost
