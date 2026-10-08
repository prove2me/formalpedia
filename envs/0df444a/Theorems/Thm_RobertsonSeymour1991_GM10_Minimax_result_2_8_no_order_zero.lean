-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_2_8_no_order_zero
-- name    : RobertsonSeymour1991.GM10.Minimax.result_2_8_no_order_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:51.246703+00:00
-- url     : https://prove2.me/theorems/a67af7f0-39a4-40f8-a6c1-f86e2bc57c1a
-- title:
--   (2.8), p. 157 — no order-0 separation of B into non-null parts
-- statement:
--   Let $\mathcal T$ be a tangle of order $\theta$ in a hypergraph $G$ and let $(A,B)\in\mathcal T$ be extreme. Then there is no separation $(B_1,B_2)$ of $B$ (with $B_1\cup B_2=B$, $E(B_1\cap B_2)=\emptyset$) such that $B_1$ and $B_2$ are both non-null and
--
--   $$|V(B_1\cap B_2)|=0.$$
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances. "Non-null" means having at least one vertex (a null hypergraph has no vertices), written as nonemptiness of the vertex sets.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 157, (2.8), "In particular", first part

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace RobertsonSeymour1991.GM10.Minimax

/-- (2.8), p. 157, "In particular", first part: if `𝒯` is a tangle of order `θ` in `G` and `(A, B) ∈ 𝒯`
is extreme, there is no separation `(B₁, B₂)` of `B` with `B₁, B₂` non-null (having a vertex) of
order `0`. -/
theorem result_2_8_no_order_zero {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B : G.Sub)
    (hext : Hypergraph.IsExtreme 𝒯 A B) :
    ¬ ∃ B₁ B₂ : G.Sub, B₁.union B₂ = B ∧ B₁.edges ∩ B₂.edges = ∅ ∧
      B₁.verts.Nonempty ∧ B₂.verts.Nonempty ∧ Hypergraph.order B₁ B₂ = 0 := by sorry

end RobertsonSeymour1991.GM10.Minimax
