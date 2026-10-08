-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_2_2
-- name    : RobertsonSeymour1991.GM10.Minimax.result_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:37.838664+00:00
-- url     : https://prove2.me/theorems/5bd3d9c9-6e46-4bfa-bd75-8fa6111b1653
-- title:
--   (2.2), p. 155 — (A ∪ A′, B ∩ B′) ∈ 𝒯 when it has order < θ
-- statement:
--   Let $\mathcal T$ be a tangle of order $\theta$ in a hypergraph $G$, and let $(A,B),(A',B')\in\mathcal T$. If the separation $(A\cup A',\,B\cap B')$ has order $<\theta$, then
--
--   $$(A\cup A',\,B\cap B')\in\mathcal T.$$
--
--   This closure property lets one enlarge the "small side" of a tangle's separations; it is used in the proof of (2.3).
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances. The pair $(A\cup A',B\cap B')$ is always a separation of $G$, so only its order is assumed.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 155, (2.2)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace RobertsonSeymour1991.GM10.Minimax

/-- (2.2), p. 155: if `𝒯` is a tangle of order `θ`, `(A, B), (A', B') ∈ 𝒯` and `(A ∪ A', B ∩ B')` has
order `< θ`, then `(A ∪ A', B ∩ B') ∈ 𝒯`. -/
theorem result_2_2 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B A' B' : G.Sub)
    (hAB : (A, B) ∈ 𝒯) (hA'B' : (A', B') ∈ 𝒯)
    (hord : Hypergraph.order (A.union A') (B.inter B') < θ) :
    (A.union A', B.inter B') ∈ 𝒯 := by sorry

end RobertsonSeymour1991.GM10.Minimax
