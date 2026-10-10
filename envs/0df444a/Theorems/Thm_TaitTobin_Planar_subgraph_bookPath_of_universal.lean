-- Prove2me | Theorems.Thm_TaitTobin_Planar_subgraph_bookPath_of_universal
-- name    : TaitTobin.Planar.subgraph_bookPath_of_universal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:51.800005+00:00
-- url     : https://prove2.me/theorems/1edbc1e8-70b6-4f76-b331-174f8ffa3880
-- title:
--   Proof of Theorem 15, p. 13 — a planar graph with two universal vertices is a spanning subgraph of K₂ + Pₙ₋₂
-- statement:
--   Let $G$ be a planar graph on $n$ vertices and let $x \ne w$ be two vertices each adjacent to every other vertex. Then, after relabelling the vertices of $G$, $G$ is a spanning subgraph of $K_2 + P_{n-2}$: there is a bijection $e$ from $V(G)$ to the vertex set of $K_2 + P_{n-2}$ such that
--   $$a \sim_G b \implies e(a) \sim e(b) \text{ in } K_2 + P_{n-2}.$$
--
--   This is the combinatorial core of the last step of the proof of Theorem 15: the remaining $n-2$ vertices induce a disjoint union of paths and isolated vertices, which fits inside a single path.
--
--   **Formalization Note** The statement concerns every planar graph with two universal vertices, not only the extremal one; the final comparison with $K_2 + P_{n-2}$ via strict monotonicity of $\lambda_1$ is left to the goal theorem.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 13, proof of Theorem 15

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Proof of Theorem 15, p. 13: a planar graph on `n` vertices with two distinct vertices `x`, `w`
each adjacent to every other vertex is, after relabelling its vertices, a spanning subgraph of
`K₂ + Pₙ₋₂`. -/
theorem subgraph_bookPath_of_universal {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (x w : Fin n) (hxw : x ≠ w) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y)
    (hw : ∀ y : Fin n, y ≠ w → G.Adj w y) :
    ∃ e : Fin n ≃ (Fin 2 ⊕ Fin (n - 2)),
      ∀ a b : Fin n, G.Adj a b → (bookPath n).Adj (e a) (e b) := by sorry
end TaitTobin.Planar
