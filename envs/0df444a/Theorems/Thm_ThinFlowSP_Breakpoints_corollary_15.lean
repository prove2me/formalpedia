-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_corollary_15
-- name    : ThinFlowSP.Breakpoints.corollary_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:37.670658+00:00
-- url     : https://prove2.me/theorems/622b8748-cbed-4310-9c93-290e4e7310c0
-- title:
--   Corollary 15, p. 10 — the labels are determined by the flow value and the label at s
-- statement:
--   Let $G' = (V, A', A^*)$ be a shortest path graph with resetting with $s \ne t$ and $\nu \in \mathbb R^{A'}_{>0}$ capacities. If $x'$ and $\hat x'$ are normalized thin $s$–$t$-flows with resetting of the same value, with corresponding labels $\ell'$ and $\hat\ell'$ such that $\ell'_s = \hat\ell'_s$, then
--   $$\ell' = \hat\ell' .$$
--
--   The flow itself need not be unique (Example 16); the labels are, which makes $\varrho^{G'}$ a function.
--
--   **Formalization Note** The hypothesis $s \ne t$ is the paper's standing assumption on source and sink (§2).
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 10, Corollary 15

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem corollary_15 (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a)
    (x xh : G.A → ℝ) (l lh : G.V → ℝ) (val : ℝ)
    (hx : IsStaticFlow G x val) (hxh : IsStaticFlow G xh val)
    (hl : IsThinFlowLabels G Astar ν x l) (hlh : IsThinFlowLabels G Astar ν xh lh)
    (hs : l G.s = lh G.s) :
    l = lh := by sorry

end ThinFlowSP.Breakpoints
