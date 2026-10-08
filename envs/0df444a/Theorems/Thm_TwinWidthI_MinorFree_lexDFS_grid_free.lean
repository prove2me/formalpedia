-- Prove2me | Theorems.Thm_TwinWidthI_MinorFree_lexDFS_grid_free
-- name    : TwinWidthI.MinorFree.lexDFS_grid_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:58.488981+00:00
-- url     : https://prove2.me/theorems/61f949e2-9b74-4e61-9f82-6574291ec05e
-- title:
--   pp. 3:26–3:29 — the Lex-DFS order of a K_t-minor-free graph is g(t)-grid free
-- statement:
--   Let $t\ge0$, let $G$ be a finite connected graph with no $K_t$ minor, and let $v_1,\dots,v_n$ be any Lex-DFS discovery order of $G$ (with its DFS tree). Let $M=A_\sigma(G)$ be the $0/1$ adjacency matrix of $G$ with rows and columns in this order. Then $M$ has no $g(t)$-grid minor, where
--
--   $$
--   g(t)=2\bigl(2^{4t+1}+2\bigr)^2 :
--   $$
--
--   there is no division of the rows into $g(t)$ nonempty consecutive intervals and of the columns into $g(t)$ nonempty consecutive intervals such that every one of the $g(t)^2$ zones contains a $1$.
--
--   This is the heart of the proof of Theorem 6.3: a $g(t)$-grid minor in the Lex-DFS order would yield a $K_{t,t}$-minor, hence a $K_t$-minor.
--
--   **Formalization Note** The proof's value $g(t)=2h(t)^2$, $h(t)=2^{4t+1}+2$ (p. 3:26) is used; the theorem statement prints $2(2^{4t+1}+1)^2$. The Lex-DFS is the predicate of the LexDFS definition file; connectedness is the proof's reduction to connected components. The statement holds for every Lex-DFS (any start vertex and any choice among tied components), as in the paper; that some Lex-DFS exists is the separate item `lexDFS_exists`.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:26–3:29, proof of Theorem 6.3, "We will show that M is g(t)-mixed free, actually even g(t)-grid free" (p. 3:26) and "Hence the adjacency matrix M is g(t)-mixed free, and even g(t)-grid free" (p. 3:29)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
import Definitions.Def_TwinWidthI_MinorFree_Setting
import Definitions.Def_TwinWidthI_MinorFree_LexDFS

namespace TwinWidthI.MinorFree

/-- pp. 3:26–3:29: for a connected `K_t`-minor free graph `G`, the adjacency matrix of `G` in
any Lex-DFS discovery order `σ` has no `g(t)`-grid minor, `g(t) = 2(2^{4t+1}+2)^2`. -/
theorem lexDFS_grid_free (t : ℕ) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hG : ¬ RobertsonSeymour1986.GM5.IsMinor (⊤ : SimpleGraph (Fin t)) G)
    {n : ℕ} (σ : V ≃ Fin n) (par : V → V) (hlex : IsLexDFSOrder G σ par) :
    ¬ TwinWidthI.GridThm.HasGridMinor (adjMat G σ) (gMF t) := by sorry

end TwinWidthI.MinorFree
