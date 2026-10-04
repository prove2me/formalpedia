-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_lyapunov_positive_recurrent
-- name    : SennottDP.MarkovCost.lyapunov_positive_recurrent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:55:09.206586+00:00
-- url     : https://prove2.me/theorems/65e4af32-f1e2-4cd5-a3dd-8908b6a39732
-- title:
--   Corollary C.1.6 — a Lyapunov function with drift $-\epsilon$ off $z$ makes $z$ positive recurrent
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ with a distinguished state $z$. Suppose there are a finite nonnegative function $y$ on $S$ and $\epsilon > 0$ with
--   $$ \sum_j P_{zj}\, y(j) < \infty, \qquad \sum_j P_{ij}\,[y(j) - y(i)] \le -\epsilon, \quad i \ne z. \tag{C.10}$$
--   Then $P(T_{iz} < \infty) = 1$ for all $i$, $m_{iz} \le y(i)/\epsilon$ for $i \ne z$, and $m_{zz} < \infty$; hence $z$ is positive recurrent.
--
--   It is the first half of the Lyapunov criterion for a chain to be $z$ standard.
--
--   **Formalization Note** The drift condition is written $\sum_j P_{ij}\, y(j) + \epsilon \le y(i)$ for $i \ne z$, equivalent to (C.10) because $y$ is finite; all sums are in $[0,\infty]$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 297, Corollary C.1.6, Eq. (C.10)

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Corollary C.1.6, p. 297. Let `z` be a distinguished state, `y` a finite
nonnegative function on `S` and `ε > 0` with `∑_j P_{zj} y(j) < ∞` and (C.10)
`∑_j P_{ij}[y(j) − y(i)] ≤ −ε` for `i ≠ z` (written `∑_j P_{ij} y(j) + ε ≤ y(i)`). Then
`P(T_{iz} < ∞) = 1` for all `i`, `m_{iz} ≤ y(i)/ε` for `i ≠ z`, and `m_{zz} < ∞`, so that `z` is
positive recurrent. -/
theorem lyapunov_positive_recurrent {S : Type} [Countable S] (M : MC S) (z : S) (y : S → ℝ≥0)
    (ε : ℝ≥0) (hε : 0 < ε) (hz : ∑' j, M.P z j * (y j : ℝ≥0∞) < ⊤)
    (hdrift : ∀ i, i ≠ z → ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) :
    (∀ i, hitProb M {z} i = 1) ∧
    (∀ i, i ≠ z → meanPassage M {z} i ≤ (y i : ℝ≥0∞) / ε) ∧
    meanPassage M {z} z < ⊤ ∧ PositiveRecurrent M z := by sorry

end SennottDP.MarkovCost
