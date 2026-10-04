-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_lyapunov_return_cost_finite
-- name    : SennottDP.MarkovCost.lyapunov_return_cost_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T14:06:29.485104+00:00
-- url     : https://prove2.me/theorems/e8e755c9-e9d5-46b7-b982-75e080320d44
-- title:
--   Corollary C.2.4 — the drift condition (C.16) gives $c_{iz} \le r(i) + F m_{iz}$ and $c_{zz} < \infty$
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ with finite nonnegative costs $C(i)$, and let $z$ be a distinguished state with $m_{iz} < \infty$ for all $i$. Suppose there are a finite nonnegative function $r$ on $S$ and a finite set $H^*$ containing $z$ with
--   $$ \sum_j P_{ij}\, r(j) < \infty, \quad i \in H^*, \qquad \sum_j P_{ij}\,[r(j) - r(i)] \le -C(i), \quad i \notin H^*. \tag{C.16}$$
--   Then there is a finite nonnegative constant $F$ such that $c_{iz} \le r(i) + F\, m_{iz}$ for $i \ne z$. If $H^* = \{z\}$, then $c_{iz} \le r(i)$ for $i \ne z$. Finally $c_{zz} < \infty$.
--
--   Together with Corollary C.1.6 this gives a verifiable criterion for a chain to be $z$ standard.
--
--   **Formalization Note** The second condition of (C.16) is written $\sum_j P_{ij}\, r(j) + C(i) \le r(i)$ in $[0,\infty]$, equivalent since $r$ is finite; $H^*$ is a `Finset`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 300–301, Corollary C.2.4, Eq. (C.16)

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Corollary C.2.4, pp. 300–301. Assume `m_{iz} < ∞` for a distinguished state
`z` and all `i`. Let `r` be a finite nonnegative function on `S` and `H*` a finite set containing
`z` with (C.16): `∑_j P_{ij} r(j) < ∞` for `i ∈ H*` and `∑_j P_{ij}[r(j) − r(i)] ≤ −C(i)` for
`i ∉ H*` (written `∑_j P_{ij} r(j) + C(i) ≤ r(i)`). Then there is a finite nonnegative constant
`F` with `c_{iz} ≤ r(i) + F m_{iz}` for `i ≠ z`; if `H* = {z}`, then `c_{iz} ≤ r(i)` for `i ≠ z`;
finally `c_{zz} < ∞`. -/
theorem lyapunov_return_cost_finite {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (z : S)
    (hm : ∀ i, meanPassage M {z} i < ⊤) (r : S → ℝ≥0) (Hs : Finset S) (hzH : z ∈ Hs)
    (hH : ∀ i ∈ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤)
    (hdrift : ∀ i ∉ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i) :
    (∃ F : ℝ≥0, ∀ i, i ≠ z → passageCost M C {z} i ≤ r i + F * meanPassage M {z} i) ∧
    (Hs = {z} → ∀ i, i ≠ z → passageCost M C {z} i ≤ r i) ∧
    passageCost M C {z} z < ⊤ := by sorry

end SennottDP.MarkovCost
