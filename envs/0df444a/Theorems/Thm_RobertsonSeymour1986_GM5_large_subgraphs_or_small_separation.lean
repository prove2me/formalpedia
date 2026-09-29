-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_large_subgraphs_or_small_separation
-- name    : RobertsonSeymour1986.GM5.large_subgraphs_or_small_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:03:12.21957+00:00
-- url     : https://prove2.me/theorems/1957d796-244e-4410-a050-c36eb39212f2
-- title:
--   (6.4) $k$ disjoint large connected subgraphs, or a small balanced separation
-- statement:
--   Let $G$ be a finite graph and let $k>0$ be an integer. Then at least one of the following holds:
--
--   1. there are $k$ disjoint connected subgraphs of $G$, each with at least
--   $$\frac{4(3^k-1)^{-1}|V(G)|}{3}$$
--   vertices;
--   2. there is a separation $(V_1,V_2)$ of $G$ with $|V_1\cap V_2|<k$ and
--   $$|V_1-V_2|,\ |V_2-V_1|\le \tfrac23|V(G)|.$$
--
--   With (5.3) and (3.2), this is used in (7.1) to find a balanced separation of bounded order in every graph without a $\theta$-grid minor.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (6.4), p. 106 (PDF p. 15); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsSeparation

namespace RobertsonSeymour1986.GM5

/-- (6.4): every graph has either `k` disjoint large connected subgraphs, or a separation of order
less than `k` with both sides of size at most `2|V(G)|/3`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (6.4), p. 106 (PDF p. 15): "Let G be a graph and let k > 0 be an integer. Then at least one
of the following holds: (i) there are k disjoint connected subgraphs of G, each with at least
4(3^k − 1)^{−1}|V(G)|/3 vertices; (ii) there is a separation (V₁, V₂) of G such that |V₁ ∩ V₂| < k
and |V₁ − V₂|, |V₂ − V₁| ≤ 2|V(G)|/3."

**Formalization Note** No `θ`. The bounds are compared in `ℚ`. `G` need not be connected. -/
theorem large_subgraphs_or_small_separation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (hk : 0 < k) :
    (∃ B : Fin k → G.Subgraph, (∀ i, (B i).Connected) ∧
        Pairwise (fun i i' => Disjoint (B i).verts (B i').verts) ∧
        ∀ i, 4 * ((3 : ℚ) ^ k - 1)⁻¹ * (Fintype.card V : ℚ) / 3 ≤ ((B i).verts.ncard : ℚ)) ∨
    (∃ V₁ V₂ : Finset V, IsSeparation G V₁ V₂ ∧ (V₁ ∩ V₂).card < k ∧
        ((V₁ \ V₂).card : ℚ) ≤ 2 * (Fintype.card V : ℚ) / 3 ∧
        ((V₂ \ V₁).card : ℚ) ≤ 2 * (Fintype.card V : ℚ) / 3) := by sorry

end RobertsonSeymour1986.GM5
