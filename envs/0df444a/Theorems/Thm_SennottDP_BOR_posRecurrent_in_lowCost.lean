-- Prove2me | Theorems.Thm_SennottDP_BOR_posRecurrent_in_lowCost
-- name    : SennottDP.BOR.posRecurrent_in_lowCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:30:15.180313+00:00
-- url     : https://prove2.me/theorems/ca4636f6-01a1-4b53-ae57-7a73e91b5f9f
-- title:
--   Proposition 7.5.5 — an optimal stationary policy has a positive recurrent low-cost state
-- statement:
--   Assume that the minimum average cost is a finite constant $J$, $J(i)=J$ for all $i$, and that $e$ is an average cost optimal stationary policy. Assume that for some state $i$ and $\varepsilon>0$ the set $G=\{j\mid C(j,e)\le J+\varepsilon\}$ satisfies
--   $$
--   \lim_{n\to\infty}\sum_{j\in G}Q^{(n)}_{ij}(e)=\sum_{j\in G}\lim_{n\to\infty}Q^{(n)}_{ij}(e).\qquad(7.33)
--   $$
--   Then the Markov chain induced by $e$ has at least one positive recurrent state $j\in G$, and $i$ leads to $j$.
--
--   Condition (7.33) holds automatically when $G$ is finite. The result is independent of the (SEN) assumptions.
--
--   **Formalization Note** (7.33) is stated as: the limits $q_j=\lim_nQ^{(n)}_{ij}(e)$ exist for $j\in G$ and $\sum_{j\in G}Q^{(n)}_{ij}(e)\to\sum_{j\in G}q_j$ (the book notes that these limits always exist). $J$ is a finite nonnegative constant.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 144, Proposition 7.5.5, (7.33)

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Proposition 7.5.5, p. 144. Assume the minimum average cost is a (finite)
constant `J` and `e` is an average cost optimal stationary policy. Assume that for some state `i`
and `ε > 0` the set `G = {j | C(j,e) ≤ J + ε}` satisfies (7.33),
`lim_n ∑_{j∈G} Q^{(n)}_{ij}(e) = ∑_{j∈G} lim_n Q^{(n)}_{ij}(e)` (the limits `q_j` of `Q^{(n)}_{ij}(e)`
exist and the limit of the sum exists and equals `∑_{j∈G} q_j`). Then the Markov chain induced by
`e` has at least one positive recurrent state `j ∈ G`, and `i` leads to `j`. -/
theorem posRecurrent_in_lowCost {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (J : ℝ≥0)
    (hJ : ∀ i, avgValue M i = J) (e : StationaryPolicy M) (he : IsAvgOptimal e.toPolicy)
    (i : S) (ε : ℝ) (hε : 0 < ε) (G : Set S)
    (hG : G = lowCostSetOf M e ((J : ℝ≥0∞) + ENNReal.ofReal ε)) (q : S → ℝ≥0∞)
    (hq : ∀ j ∈ G, Tendsto (fun n => Qavg e.toPolicy n i j) atTop (𝓝 (q j)))
    (h733 : Tendsto (fun n => ∑' j : G, Qavg e.toPolicy n i j) atTop (𝓝 (∑' j : G, q j))) :
    ∃ j ∈ G, PosRecurrent e.toPolicy j ∧ LeadsTo e.toPolicy i j := by sorry

end SennottDP.BOR
