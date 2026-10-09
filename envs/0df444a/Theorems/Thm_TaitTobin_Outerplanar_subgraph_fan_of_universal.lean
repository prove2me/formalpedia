-- Prove2me | Theorems.Thm_TaitTobin_Outerplanar_subgraph_fan_of_universal
-- name    : TaitTobin.Outerplanar.subgraph_fan_of_universal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:16.90199+00:00
-- url     : https://prove2.me/theorems/97942d5f-9de0-4f03-81b5-146724647628
-- title:
--   Proof of Theorem 7, p. 7 — an outerplanar graph with a dominating vertex x is a spanning subgraph of K₁ + Pₙ₋₁
-- statement:
--   Let $G$ be an outerplanar graph on $n$ vertices and let $x$ be a vertex adjacent to every other vertex of $G$. Then $G$ is a spanning subgraph of the fan $K_1 + P_{n-1}$: there is a bijection $e$ from $V(G)$ onto the vertex set of $K_1 + P_{n-1}$ such that
--   $$uw \in E(G) \implies e(u)\,e(w) \in E(K_1 + P_{n-1}).$$
--
--   Once $x$ is known to be adjacent to all other vertices, this reduces Theorem 7 to the monotonicity of $\lambda_1$ under strict subgraphs.
--
--   **Formalization Note** The bijection is between $\{0,\dots,n-1\}$ and $\mathrm{Fin}\,1 \sqcup \mathrm{Fin}(n-1)$, the vertex type of the fan; $n \ge 1$ follows from the existence of $x$. The statement is about every outerplanar graph with a dominating vertex, not only the spectral maximizer, which is how the paper's argument uses it.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 7, proof of Theorem 7, last paragraph

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace TaitTobin.Outerplanar

open Classical WangKangXue.SpectralTuran

/-- Proof of Theorem 7, p. 7: an outerplanar graph on `n` vertices with a vertex `x` adjacent to
every other vertex is, after relabelling its vertices, a spanning subgraph of the fan
`K₁ + Pₙ₋₁`. -/
theorem subgraph_fan_of_universal {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (x : Fin n) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y) :
    ∃ e : Fin n ≃ (Fin 1 ⊕ Fin (n - 1)),
      ∀ a b : Fin n, G.Adj a b → (fan n).Adj (e a) (e b) := by sorry
end TaitTobin.Outerplanar
