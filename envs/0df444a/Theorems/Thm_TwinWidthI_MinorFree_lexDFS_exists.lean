-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_lexDFS_exists
-- name    : TwinWidthI.MinorFree.lexDFS_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:56.503033+00:00
-- url     : https://prove2.me/theorems/8aabfefd-a2bc-491a-9c65-f3bf68cf6e69
-- title:
--   p. 3:26 — a Lex-DFS can be performed from any vertex of a connected graph
-- statement:
--   Let $G$ be a finite connected graph and $v_1$ any vertex of $G$. Then there is a Lex-DFS discovery order of $G$ starting at $v_1$: an ordering $v_1,\dots,v_n$ of all vertices with a DFS tree $\mathcal T$ such that each new vertex is a neighbour of the current active vertex, chosen in a component of the undiscovered vertices with lexicographically maximal word,
--
--   $$
--   \exists\,(\sigma,\mathcal T)\ \text{Lex-DFS of }G\ \text{with}\ \sigma^{-1}(0)=v_1 .
--   $$
--
--   The proof of Theorem 6.3 orders the adjacency matrix by this discovery order; the statement says that the search is well defined ("since $G$ is connected, the active vertex is always well-defined").
--
--   **Formalization Note** The discovery order is an equivalence $V\simeq\mathrm{Fin}\,|V|$, with $v_1$ at position $0$.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:26, proof of Theorem 6.3, "Definition of the appropriate Lex-DFS"

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_LexDFS

namespace TwinWidthI.MinorFree

/-- p. 3:26: from an arbitrary vertex `v₁` of a connected finite graph the Lex-DFS can be
performed: there is a Lex-DFS discovery order `σ` with DFS tree `par` that starts at `v₁`. -/
theorem lexDFS_exists {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (v₁ : V) :
    ∃ (σ : V ≃ Fin (Fintype.card V)) (par : V → V),
      IsLexDFSOrder G σ par ∧ (σ v₁ : ℕ) = 0 := by sorry

end TwinWidthI.MinorFree
