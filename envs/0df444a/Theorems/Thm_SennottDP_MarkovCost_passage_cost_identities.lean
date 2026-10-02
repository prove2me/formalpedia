-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_passage_cost_identities
-- name    : SennottDP.MarkovCost.passage_cost_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T14:02:08.360582+00:00
-- url     : https://prove2.me/theorems/6e874559-4fc7-46c2-b335-2c5870d04d0d
-- title:
--   Proposition C.2.2 — first passage cost identities, (C.13), and $J_R = \sum_{i\in G}\pi_i c_{iG}$
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ with finite nonnegative costs $C(i)$, and let $G \subseteq S$ be nonempty.
--
--   1. If $m_{iG} < \infty$, then $c_{iG} = \sum_k C(k)\, {}_G u_{ik}$.
--   2. If $m_{iG} < \infty$, then
--   $$ c_{iG} = C(i) + \sum_{j \notin G} P_{ij}\, c_{jG}. \tag{C.13}$$
--   3. If $G$ is contained in a positive recurrent class $R$, then $J_R = \sum_{i \in G} \pi_i c_{iG}$.
--   4. If $R$ is a positive recurrent class with $J_R < \infty$, then $c_{ij} < \infty$ for all $i, j \in R$.
--
--   These are the cost counterparts of the first passage time identities of Proposition C.1.4.
--
--   **Formalization Note** In (C.13) a term with $P_{ij} = 0$ contributes $0$; whenever $P_{ij} > 0$, $m_{jG} < \infty$ follows from $m_{iG} < \infty$, so every $c_{jG}$ that matters is the book's first passage cost. Values are in $[0,\infty]$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 299, Proposition C.2.2, Eq. (C.13)

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.2.2, p. 299. Let `G` be a nonempty subset of `S`.
(i) If `m_{iG} < ∞`, then `c_{iG} = ∑_k C(k) _G u_{ik}`.
(ii) Under the hypothesis of (i), (C.13) `c_{iG} = C(i) + ∑_{j ∉ G} P_{ij} c_{jG}`.
(iii) If `G` is contained in a positive recurrent class `R`, then `J_R = ∑_{i ∈ G} π_i c_{iG}`.
(iv) If `R` is a positive recurrent class with `J_R < ∞`, then `c_{ij} < ∞` for all `i, j ∈ R`. -/
theorem passage_cost_identities {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (G : Set S)
    (hG : G.Nonempty) :
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = ∑' k, (C k : ℝ≥0∞) * visits M G i k) ∧
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = (C i : ℝ≥0∞) + ∑' j : ↥Gᶜ, M.P i j * passageCost M C G j) ∧
    (∀ R : Set S, IsPosRecClass M R → G ⊆ R →
      classAvgCost M C R = ∑' i : G, steadyState M i * passageCost M C G i) ∧
    (∀ R : Set S, IsPosRecClass M R → classAvgCost M C R < ⊤ →
      ∀ i ∈ R, ∀ j ∈ R, passageCost M C {j} i < ⊤) := by sorry

end SennottDP.MarkovCost
