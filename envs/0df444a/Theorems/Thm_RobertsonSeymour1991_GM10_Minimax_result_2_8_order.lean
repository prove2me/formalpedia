-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_2_8_order
-- name    : RobertsonSeymour1991.GM10.Minimax.result_2_8_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:47.439175+00:00
-- url     : https://prove2.me/theorems/ab571a00-4972-454c-9d38-bc264a31020e
-- title:
--   (2.8), p. 157 — an extreme separation of a tangle of order θ has order θ − 1
-- statement:
--   Let $\mathcal T$ be a tangle of order $\theta$ in a hypergraph $G$, and let $(A,B)\in\mathcal T$ be extreme. Then
--
--   $$|V(A\cap B)|=\theta-1.$$
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances. Since $\theta\ge1$ for a tangle, $\theta-1$ in $\mathbb N$ is the true difference.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 157, (2.8), first sentence

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace RobertsonSeymour1991.GM10.Minimax

/-- (2.8), p. 157, first sentence: if `𝒯` is a tangle of order `θ` in `G` and `(A, B) ∈ 𝒯` is extreme,
then `(A, B)` has order `θ − 1`. -/
theorem result_2_8_order {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B : G.Sub)
    (hext : Hypergraph.IsExtreme 𝒯 A B) :
    Hypergraph.order A B = θ - 1 := by sorry

end RobertsonSeymour1991.GM10.Minimax
