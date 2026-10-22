-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_corollary_8
-- name    : ThinFlowSP.Breakpoints.corollary_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:30.759519+00:00
-- url     : https://prove2.me/theorems/d2c223b0-8990-42a1-be06-aab1663c18e1
-- title:
--   Corollary 8, p. 7 — normalizing the labels of an (LCP) solution gives a normalized thin flow
-- statement:
--   Let $G' = (V, A', A^*)$ be a shortest path graph with resetting with $s \ne t$, $\nu \in \mathbb R^{A'}_{>0}$ capacities, $\nu'_0 \ge 0$ an inflow rate and $\ell'_0 \ge 0$ a label. If $z' = (\ell', x', y')$ solves (LCP),
--   $$z' \ge 0,\qquad Mz' - \ell'_0\mathbb 1_s - \nu'_0\mathbb 1_t \ge 0,\qquad z'^\top(Mz' - \ell'_0\mathbb 1_s - \nu'_0\mathbb 1_t) = 0,$$
--   then $x'$ is a normalized thin $s$–$t$-flow with resetting of value $\nu'_0$, $\pi(\ell')$ are corresponding labels, and $\pi(\ell')_s = \ell'_0$.
--
--   Together with Lemma 9, this lets the theory of linear complementarity problems with $P_0$-matrices produce normalized thin flows.
--
--   **Formalization Note** The hypothesis $s \ne t$ is the paper's standing assumption on source and sink (§2).
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 7, Corollary 8

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem corollary_8 (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a)
    (nu0 l0 : ℝ) (hnu0 : 0 ≤ nu0) (hl0 : 0 ≤ l0)
    (l : G.V → ℝ) (x : G.A → ℝ) (y : {a : G.A // a ∉ Astar} → ℝ)
    (hz : SolvesLCP (lcpMatrix G Astar ν) (lcpRhs G Astar nu0 l0) (Sum.elim l (Sum.elim x y))) :
    IsStaticFlow G x nu0 ∧ IsThinFlowLabels G Astar ν x (normalize G Astar l) ∧
      normalize G Astar l G.s = l0 := by sorry

end ThinFlowSP.Breakpoints
