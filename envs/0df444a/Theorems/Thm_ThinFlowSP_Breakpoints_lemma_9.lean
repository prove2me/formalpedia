-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_lemma_9
-- name    : ThinFlowSP.Breakpoints.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:33.016775+00:00
-- url     : https://prove2.me/theorems/ea84d6f6-091c-4403-ac42-9031e0c1f82a
-- title:
--   Lemma 9, p. 7 — all principal minors of the LCP matrix M are non-negative
-- statement:
--   Let $G' = (V, A', A^*)$ be a shortest path graph with resetting, $\nu \in \mathbb R^{A'}_{>0}$ capacities and $M$ the matrix of (LCP), indexed by $V \uplus A' \uplus (A'\setminus A^*)$. Then for every index set $S$,
--   $$\det\bigl(M_{S,S}\bigr) \ge 0,$$
--   that is, $M$ is a $P_0$-matrix.
--
--   With the uniqueness of the trivial solution for $\nu'_0 = \ell'_0 = 0$, this gives existence of solutions of (LCP) (Theorem 13).
--
--   **Formalization Note** The paper's determinant of a matrix over an unordered finite index set (p. 7) is `Matrix.det` over the finite type of elements of $S$.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 7, Lemma 9

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem lemma_9 (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hν : ∀ a, 0 < ν a) (S : Finset (Idx G Astar)) :
    0 ≤ ((lcpMatrix G Astar ν).submatrix (fun i : S => i.1) (fun i : S => i.1)).det := by sorry

end ThinFlowSP.Breakpoints
