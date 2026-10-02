-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_lyapunov_passage_bound
-- name    : SennottDP.MarkovCost.lyapunov_passage_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T13:52:18.367568+00:00
-- url     : https://prove2.me/theorems/a91674d3-dc3b-4839-8f83-a651da8d9b0d
-- title:
--   Proposition C.1.5 — a Lyapunov drift of $-\epsilon$ off $G$ gives $m_{iG} \le y(i)/\epsilon$
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ and $G \subseteq S$ nonempty. Suppose there are a finite nonnegative function $y$ on $S$ and $\epsilon > 0$ with
--   $$ \sum_j P_{ij}\,[y(j) - y(i)] \le -\epsilon, \qquad i \notin G. \tag{C.7}$$
--   Then for every $i \notin G$ the chain started at $i$ reaches $G$ with probability one, $P(T_{iG} < \infty) = 1$, and
--   $$ m_{iG} \le \frac{y(i)}{\epsilon}. $$
--
--   This is the Foster–Lyapunov criterion for finiteness of expected first passage times.
--
--   **Formalization Note** Since $y$ is finite and $\sum_j P_{ij} = 1$, (C.7) is equivalent to $\sum_j P_{ij}\, y(j) + \epsilon \le y(i)$ (the left side of (C.7) is $+\infty$ when $\sum_j P_{ij} y(j) = \infty$); this form is used, in $[0,\infty]$. $y$ is `ℝ≥0`-valued and $\epsilon \in \mathbb R_{>0}$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 296–297, Proposition C.1.5, Eq. (C.7)

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.1.5, pp. 296–297. Let `G` be a nonempty subset of `S`, `y` a
finite nonnegative function on `S` and `ε > 0` with (C.7) `∑_j P_{ij}[y(j) − y(i)] ≤ −ε` for
`i ∉ G`, written equivalently as `∑_j P_{ij} y(j) + ε ≤ y(i)` (the left side of (C.7) is `+∞` when
`∑_j P_{ij} y(j) = ∞`). Then for `i ∉ G`, `P(T_{iG} < ∞) = 1` and `m_{iG} ≤ y(i)/ε`. -/
theorem lyapunov_passage_bound {S : Type} [Countable S] (M : MC S) (G : Set S)
    (hG : G.Nonempty) (y : S → ℝ≥0) (ε : ℝ≥0) (hε : 0 < ε)
    (hdrift : ∀ i ∉ G, ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) :
    ∀ i ∉ G, hitProb M G i = 1 ∧ meanPassage M G i ≤ (y i : ℝ≥0∞) / ε := by sorry

end SennottDP.MarkovCost
