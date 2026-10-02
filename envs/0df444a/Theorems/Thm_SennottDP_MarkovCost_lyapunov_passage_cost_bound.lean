-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_lyapunov_passage_cost_bound
-- name    : SennottDP.MarkovCost.lyapunov_passage_cost_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T14:04:11.840222+00:00
-- url     : https://prove2.me/theorems/bec8c4a2-9419-4c70-80c5-4b8ba34c34c9
-- title:
--   Proposition C.2.3 — a cost drift condition (C.14) bounds $c_{iG}$ by $r(i) + F m_{iG}$
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ with finite nonnegative costs $C(i)$. Let $G \subseteq S$ be nonempty with $m_{iG} < \infty$ for all $i \notin G$. Suppose there are a finite nonnegative function $r$ on $S$ and a finite set $H \subseteq S - G$ with
--   $$ \sum_j P_{ij}\,[r(j) - r(i)] \le -C(i), \quad i \notin G \cup H, \qquad \sum_j P_{ij}\, r(j) < \infty, \quad i \in H. \tag{C.14}$$
--   Then there is a finite nonnegative constant $F$ such that
--   $$ c_{iG} \le r(i) + F\, m_{iG}, \qquad i \notin G. $$
--   If $H = \emptyset$, then $c_{iG} \le r(i)$ for $i \notin G$.
--
--   This is the Lyapunov criterion for finiteness of expected first passage costs.
--
--   **Formalization Note** Because $r$ is finite, the first condition of (C.14) is written $\sum_j P_{ij}\, r(j) + C(i) \le r(i)$ in $[0,\infty]$. $H$ is a `Finset` disjoint from $G$; $F$ is an `ℝ≥0` constant chosen before $i$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 300, Proposition C.2.3, Eq. (C.14)

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.2.3, p. 300. Let `G` be a nonempty subset of `S` with
`m_{iG} < ∞` for all `i ∉ G`. Let `r` be a finite nonnegative function on `S` and `H ⊆ S − G` a
finite set with (C.14): `∑_j P_{ij}[r(j) − r(i)] ≤ −C(i)` for `i ∉ G ∪ H` (written
`∑_j P_{ij} r(j) + C(i) ≤ r(i)`) and `∑_j P_{ij} r(j) < ∞` for `i ∈ H`. Then there is a finite
nonnegative constant `F` with `c_{iG} ≤ r(i) + F m_{iG}` for `i ∉ G`; if `H = ∅`, then
`c_{iG} ≤ r(i)` for `i ∉ G`. -/
theorem lyapunov_passage_cost_bound {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0)
    (G : Set S) (hG : G.Nonempty) (hm : ∀ i ∉ G, meanPassage M G i < ⊤)
    (r : S → ℝ≥0) (H : Finset S) (hHG : Disjoint (H : Set S) G)
    (hdrift : ∀ i ∉ G, i ∉ H → ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i)
    (hH : ∀ i ∈ H, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤) :
    (∃ F : ℝ≥0, ∀ i ∉ G, passageCost M C G i ≤ r i + F * meanPassage M G i) ∧
    (H = ∅ → ∀ i ∉ G, passageCost M C G i ≤ r i) := by sorry

end SennottDP.MarkovCost
