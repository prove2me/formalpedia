-- Prove2me | Theorems.Thm_TwinWidthI_BallGraph_cell_card_le
-- name    : TwinWidthI.BallGraph.cell_card_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:39.451207+00:00
-- url     : https://prove2.me/theorems/ac31e52b-49b8-4be0-a5e3-ec52345d0fe9
-- title:
--   Proof of Theorem 4.5, p. 3:16 — each cell of side $2/\sqrt d$ contains at most $k$ centres
-- statement:
--   Let $d,k\ge 0$, let $V$ be a finite set and $c:V\to\mathbb R^d$, and let $G$ be the unit ball graph with centres $c$ (distinct $u,v$ adjacent iff $\|c(u)-c(v)\|_2\le 2$). Suppose $G$ has no clique of size $k+1$. Then for every $z\in\mathbb Z^d$ the cell
--   $$Q_z=\prod_{i=1}^d\Bigl[\,z_i\tfrac{2}{\sqrt d},\ (z_i+1)\tfrac{2}{\sqrt d}\Bigr)$$
--   contains at most $k$ centres:
--   $$\bigl|\{v\in V : c(v)\in Q_z\}\bigr|\le k .$$
--
--   The bound on centres per cell is the counting fact behind the degree bound $(3\lceil\sqrt d\rceil)^d k$ in Theorem 4.5.
--
--   **Formalization Note.** Cells are half-open, so they partition $\mathbb R^d$. The count is `Set.ncard` of a subset of the finite type $V$. "Clique number $k$" is encoded as "no clique of size $k+1$" (`CliqueFree (k+1)`). For $d=0$ Lean reads $2/\sqrt 0$ as $0$ and the cell is the one-point space $\mathbb R^0$; the statement is then still true (all centres coincide and $G$ is complete), so no hypothesis $d\ge1$ is added.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:16, proof of Theorem 4.5, "Hence the unit balls centered within a given cell form a clique. In particular, each cell contains at most k centers."

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting

namespace TwinWidthI.BallGraph

/-- Proof of Theorem 4.5, p. 3:16: when the unit ball graph has no clique of size `k + 1`, each
cell of the grid of spacing `2/√d` contains at most `k` centres. -/
theorem cell_card_le (d k : ℕ) {V : Type*} [Fintype V]
    (c : V → EuclideanSpace ℝ (Fin d)) (hK : (ballGraph c).CliqueFree (k + 1))
    (z : Fin d → ℤ) :
    {v : V | c v ∈ cell z}.ncard ≤ k := by sorry

end TwinWidthI.BallGraph
