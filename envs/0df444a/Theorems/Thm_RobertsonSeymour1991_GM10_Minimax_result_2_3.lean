-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_2_3
-- name    : RobertsonSeymour1991.GM10.Minimax.result_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:45.174673+00:00
-- url     : https://prove2.me/theorems/34870e30-1514-40ae-a657-a75cf1517434
-- title:
--   (2.3), p. 155 — for a tangle of order ≥ 2, E(A₁ ∪ A₂ ∪ A₃) ≠ E(G)
-- statement:
--   Let $\mathcal T$ be a tangle in a hypergraph $G$ of order $\theta\ge2$, and let $(A_1,B_1),(A_2,B_2),(A_3,B_3)\in\mathcal T$ (not necessarily distinct). Then
--
--   $$E(A_1\cup A_2\cup A_3)\ne E(G).$$
--
--   This strengthens the second tangle axiom from subhypergraphs to edge sets; it shows that the sets $E(A)$ of a tangle of order $k+1$ form a bias in the proof of (4.3).
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 155, (2.3)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace RobertsonSeymour1991.GM10.Minimax

/-- (2.3), p. 155: if `𝒯` has order `≥ 2` and `(A₁, B₁), (A₂, B₂), (A₃, B₃) ∈ 𝒯`, then
`E(A₁ ∪ A₂ ∪ A₃) ≠ E(G)`. -/
theorem result_2_3 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (hθ : 2 ≤ θ)
    (p₁ p₂ p₃ : G.Sub × G.Sub) (h₁ : p₁ ∈ 𝒯) (h₂ : p₂ ∈ 𝒯) (h₃ : p₃ ∈ 𝒯) :
    ((p₁.1.union p₂.1).union p₃.1).edges ≠ Set.univ := by sorry

end RobertsonSeymour1991.GM10.Minimax
