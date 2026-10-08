-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_2_4
-- name    : RobertsonSeymour1991.GM10.Minimax.result_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:37.151086+00:00
-- url     : https://prove2.me/theorems/b87a4028-d8b3-4128-8e68-c3e551691c66
-- title:
--   (2.4), p. 156 — an edge of size ≥ θ defines a tangle of order θ
-- statement:
--   Let $\theta\ge1$ and let $e$ be an edge of a hypergraph $G$ of size at least $\theta$. Let $\mathcal T$ be the set of all separations $(A,B)$ of $G$ of order $<\theta$ with $e\in E(B)$. Then
--
--   $$\mathcal T\text{ is a tangle in }G\text{ of order }\theta.$$
--
--   Consequently $\theta(G)\ge\gamma(G)$, the easy inequality of (4.3).
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 156, (2.4)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace RobertsonSeymour1991.GM10.Minimax

/-- (2.4), p. 156: let `θ ≥ 1` and let `e` be an edge of `G` of size `≥ θ`. The set of all separations
`(A, B)` of `G` of order `< θ` with `e ∈ E(B)` is a tangle of order `θ`. -/
theorem result_2_4 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ) (hθ : 1 ≤ θ)
    (e : E) (he : θ ≤ G.size e) :
    G.IsTangle θ {p : G.Sub × G.Sub |
      Hypergraph.IsSeparation p.1 p.2 ∧ Hypergraph.order p.1 p.2 < θ ∧ e ∈ p.2.edges} := by sorry

end RobertsonSeymour1991.GM10.Minimax
