-- Prove2me | Theorems.Thm_SupplyChainTheory_revised_cost_identities
-- name    : SupplyChainTheory.revised_cost_identities
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:59:47.572924+00:00
-- url     : https://prove2.me/theorems/1c5940dd-0551-4a36-a262-8d333d543434
-- title:
--   Lemma 10.16: under $c'_{ij} = c_{ij} + \lambda_i + \lambda_j$, tours gain $2\sum_i\lambda_i$, optimal tours stay optimal, and a 1-tree gains $\sum_i d_i \lambda_i$
-- statement:
--   **Lemma 10.16.** Let $\lambda \in \mathbb{R}^n$ and $c'_{ij} = c_{ij} + \lambda_i + \lambda_j$ (10.31).
--
--   (a) If $\Gamma$ is a TSP tour, then $z'(\Gamma) = z(\Gamma) + 2\sum_i \lambda_i$.
--
--   (b) If $\Gamma^*$ is an optimal tour under $c$, then it is also optimal under $c'$.
--
--   (c) For any 1-tree $\hat T$, $z'(\hat T) = z(\hat T) + \sum_i d_i(\hat T)\lambda_i$, where $d_i(\hat T)$
--   is the degree of node $i$ in $\hat T$.
--
--   The book omits the proof (Problem 10.15). Every node has degree two in a tour, which gives (a)
--   and hence (b), while a 1-tree's degrees vary, which is why the revision can raise the optimal
--   1-tree length relative to the tour length and tighten the bound.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 446, Sect. 10.6.1, Lemma 10.16, Eq. (10.31)-(10.32): 'Proof. Omitted; see Problem 10.15'

import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem revised_cost_identities {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 3 ≤ n)
    (lam : Fin n → ℝ) :
    (∀ τ : Equiv.Perm (Fin n), tourLength (revisedCost c lam) τ = tourLength c τ + 2 * ∑ i, lam i)
      ∧ (∀ τ : Equiv.Perm (Fin n), IsMinOn (tourLength c) Set.univ τ →
          IsMinOn (tourLength (revisedCost c lam)) Set.univ τ)
      ∧ ∀ (r : Fin n) (G : SimpleGraph (Fin n)), Is1Tree r G →
          graphWeight (revisedCost c lam) G = graphWeight c G + ∑ i, G.degree i * lam i := by sorry

end SupplyChainTheory
