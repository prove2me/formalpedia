-- Prove2me | Theorems.Thm_SennottDP_MarkovCost_first_passage_identities
-- name    : SennottDP.MarkovCost.first_passage_identities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:49:19.969651+00:00
-- url     : https://prove2.me/theorems/f79e156c-b33b-4ce1-811f-afff5cc53ea7
-- title:
--   Proposition C.1.4 — first passage identities (C.2)–(C.4), Kac's formula on a class, finite mean passage times
-- statement:
--   Let $\Gamma$ be a Markov chain on a countable state space $S$ and $G \subseteq S$ nonempty. With $_G P^{(t)}_{ik}$ the taboo probabilities, $_G u_{ik}$ the expected number of visits to $k$ in a first passage from $i$ to $G$ and $m_{iG}$ the expected first passage time:
--
--   1. for $k \notin G$, $\;{}_G u_{ik} = \delta_{ik} + \sum_{t=1}^{\infty} {}_G P^{(t)}_{ik}$;
--   2. $m_{iG} = \sum_{k \in S} {}_G u_{ik}$;
--   3. for all $i, k \in S$,
--   $$ {}_G P^{(t+1)}_{ik} = \sum_{j \notin G} P_{ij}\, {}_G P^{(t)}_{jk}\ (t \ge 1), \qquad {}_G u_{ik} = \delta_{ik} + \sum_{j \notin G} P_{ij}\, {}_G u_{jk}, \qquad m_{iG} = 1 + \sum_{j \notin G} P_{ij} m_{jG}; $$
--   4. if $G$ is contained in a positive recurrent class $R$, then $\pi_j = \sum_{i \in G} \pi_i\, {}_G u_{ij}$ for $j \in R$ and $\sum_{i \in G} \pi_i m_{iG} = 1$;
--   5. if $R$ is a positive recurrent class, then $m_{ij} < \infty$ for all $i, j \in R$.
--
--   These are the (C.2)–(C.4) first-step equations and the class results on which the Lyapunov bounds and the cost results of Appendix C rest.
--
--   **Formalization Note** All quantities are in $[0,\infty]$ with $0\cdot\infty=0$; sums over $j \notin G$ are sums over the subtype of the complement of $G$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 295–296, Proposition C.1.4, Eqs. (C.2)–(C.4)

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

open Classical in
/-- Sennott (1999), Proposition C.1.4, pp. 295–296. Let `G` be a nonempty subset of `S`.
(i) For `k ∉ G`, `_G u_{ik} = δ_{ik} + ∑_{t ≥ 1} _G P^{(t)}_{ik}`.
(ii) `m_{iG} = ∑_{k ∈ S} _G u_{ik}`.
(iii) (C.2) `_G P^{(t+1)}_{ik} = ∑_{j ∉ G} P_{ij} _G P^{(t)}_{jk}` for `i, k ∈ S`, `t ≥ 1`;
(C.3) `_G u_{ik} = δ_{ik} + ∑_{j ∉ G} P_{ij} _G u_{jk}` for `i, k ∈ S`;
(C.4) `m_{iG} = 1 + ∑_{j ∉ G} P_{ij} m_{jG}` for `i ∈ S`.
(iv) If `G` is contained in a positive recurrent class `R`, then `π_j = ∑_{i ∈ G} π_i _G u_{ij}` for
`j ∈ R` and `∑_{i ∈ G} π_i m_{iG} = 1`.
(v) If `R` is a positive recurrent class, then `m_{ij} < ∞` for all `i, j ∈ R`. -/
theorem first_passage_identities {S : Type} [Countable S] (M : MC S) (G : Set S)
    (hG : G.Nonempty) :
    (∀ i, ∀ k ∉ G,
      visits M G i k = (if i = k then 1 else 0) + ∑' t : ℕ, taboo M G (t + 1) i k) ∧
    (∀ i, meanPassage M G i = ∑' k, visits M G i k) ∧
    ((∀ i k, ∀ t : ℕ, 1 ≤ t →
        taboo M G (t + 1) i k = ∑' j : ↥Gᶜ, M.P i j * taboo M G t j k) ∧
      (∀ i k, visits M G i k = (if i = k then 1 else 0) + ∑' j : ↥Gᶜ, M.P i j * visits M G j k) ∧
      (∀ i, meanPassage M G i = 1 + ∑' j : ↥Gᶜ, M.P i j * meanPassage M G j)) ∧
    (∀ R : Set S, IsPosRecClass M R → G ⊆ R →
      (∀ j ∈ R, steadyState M j = ∑' i : G, steadyState M i * visits M G i j) ∧
      ∑' i : G, steadyState M i * meanPassage M G i = 1) ∧
    (∀ R : Set S, IsPosRecClass M R → ∀ i ∈ R, ∀ j ∈ R, meanPassage M {j} i < ⊤) := by sorry

end SennottDP.MarkovCost
