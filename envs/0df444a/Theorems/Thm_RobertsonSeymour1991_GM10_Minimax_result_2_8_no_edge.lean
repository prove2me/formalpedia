-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_2_8_no_edge
-- name    : RobertsonSeymour1991.GM10.Minimax.result_2_8_no_edge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:56.700196+00:00
-- url     : https://prove2.me/theorems/803f91b6-af8b-49bd-a9d7-9590d079a3b8
-- title:
--   (2.8), p. 157 — no edge of B has all its ends in V(A)
-- statement:
--   Let $\mathcal T$ be a tangle of order $\theta$ in a hypergraph $G$ and let $(A,B)\in\mathcal T$ be extreme. Then there is no edge $e\in E(B)$ with all its ends in $V(A)$; that is, for every $e\in E(B)$,
--
--   $$\{\text{ends of }e\}\not\subseteq V(A).$$
--
--   In particular $B$ has no edge without ends; this is what rules out tangles of order $\ge2$ when $\gamma(G)=0$ in the proof of (4.3).
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 157, (2.8), last clause

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace RobertsonSeymour1991.GM10.Minimax

/-- (2.8), p. 157, last clause: if `𝒯` is a tangle of order `θ` in `G` and `(A, B) ∈ 𝒯` is extreme,
there is no edge of `B` with all its ends in `V(A)`. -/
theorem result_2_8_no_edge {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B : G.Sub)
    (hext : Hypergraph.IsExtreme 𝒯 A B) :
    ∀ e ∈ B.edges, ¬ G.ends e ⊆ A.verts := by sorry

end RobertsonSeymour1991.GM10.Minimax
