-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_2_5
-- name    : RobertsonSeymour1991.GM10.Minimax.result_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:46.936491+00:00
-- url     : https://prove2.me/theorems/be00de77-2eac-4ce0-a69c-b175af5fa331
-- title:
--   (2.5), p. 156 — G has a tangle iff V(G) ≠ ∅
-- statement:
--   A hypergraph $G$ has a tangle (of some order) if and only if
--
--   $$V(G)\ne\emptyset.$$
--
--   It settles the degenerate case $\gamma(G)=0$ of (4.3): then $\theta(G)=1$ exactly when $G$ has a vertex.
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances. "$G$ has a tangle" is "there are $\theta$ and $\mathcal T$ with $\mathcal T$ a tangle of order $\theta$", and $\theta\ge1$ is part of the tangle predicate.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 156, (2.5)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace RobertsonSeymour1991.GM10.Minimax

/-- (2.5), p. 156: `G` has a tangle if and only if `V(G) ≠ ∅`. -/
theorem result_2_5 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) :
    (∃ (θ : ℕ) (𝒯 : Set (G.Sub × G.Sub)), G.IsTangle θ 𝒯) ↔ Nonempty V := by sorry

end RobertsonSeymour1991.GM10.Minimax
