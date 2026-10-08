-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_2_8_separation
-- name    : RobertsonSeymour1991.GM10.Minimax.result_2_8_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:57.387319+00:00
-- url     : https://prove2.me/theorems/8e644bc7-5be1-4a49-8c28-18f4c785e21e
-- title:
--   (2.8), p. 157 — separations of the large side B of an extreme separation
-- statement:
--   Let $\mathcal T$ be a tangle of order $\theta$ in a hypergraph $G$, let $(A,B)\in\mathcal T$ be extreme, and let $(B_1,B_2)$ be a separation of $B$, that is, $B_1\cup B_2=B$ and $E(B_1\cap B_2)=\emptyset$. Then either
--
--   1. $B_1\subseteq A\cap B$ and $B_2=B$, or
--   2. $B_2\subseteq A\cap B$ and $B_1=B$, or
--   3. $$|V(B_1\cap B_2)|>\min\bigl(|V(A\cap B_1)|,\,|V(A\cap B_2)|\bigr).$$
--
--   It says that the large side of an extreme separation is well connected to the small side, which drives (2.9), (2.10) and the case $\gamma(G)=0$ of (4.3).
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances. $B_1,B_2$ are subhypergraphs of $G$; "separation of $B$" is written out rather than using the separation predicate of $G$.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 157, (2.8), "Moreover" sentence

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace RobertsonSeymour1991.GM10.Minimax

/-- (2.8), p. 157, "Moreover" sentence: if `𝒯` is a tangle of order `θ` in `G`, `(A, B) ∈ 𝒯` is extreme
and `(B₁, B₂)` is a separation of `B` (`B₁ ∪ B₂ = B`, `E(B₁ ∩ B₂) = ∅`), then either `B₁ ⊆ A ∩ B` and
`B₂ = B`, or `B₂ ⊆ A ∩ B` and `B₁ = B`, or `(B₁, B₂)` has order strictly greater than
`min(|V(A ∩ B₁)|, |V(A ∩ B₂)|)`. -/
theorem result_2_8_separation {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ)
    (𝒯 : Set (G.Sub × G.Sub)) (h𝒯 : G.IsTangle θ 𝒯) (A B : G.Sub)
    (hext : Hypergraph.IsExtreme 𝒯 A B) (B₁ B₂ : G.Sub)
    (hunion : B₁.union B₂ = B) (hdisj : B₁.edges ∩ B₂.edges = ∅) :
    (B₁.le (A.inter B) ∧ B₂ = B) ∨ (B₂.le (A.inter B) ∧ B₁ = B) ∨
      min (A.verts ∩ B₁.verts).ncard (A.verts ∩ B₂.verts).ncard < Hypergraph.order B₁ B₂ := by sorry

end RobertsonSeymour1991.GM10.Minimax
