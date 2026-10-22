-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_theorem_13
-- name    : ThinFlowSP.Breakpoints.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:26.049413+00:00
-- url     : https://prove2.me/theorems/5166fb0b-6108-4659-91c3-f68c1a49386b
-- title:
--   Theorem 13, p. 10 — existence of normalized thin flows with resetting for every value and label at s
-- statement:
--   Let $G' = (V, A', A^*)$ be a shortest path graph with resetting with $s \ne t$ and $\nu \in \mathbb R^{A'}_{>0}$ capacities. For all $\nu'_0, \ell'_0 \ge 0$ there are a static $s$–$t$-flow $x'$ of value $\nu'_0$ and corresponding labels $\ell'$ (Definition 4) with
--   $$\ell'_s = \ell'_0 .$$
--
--   Existence for every flow value is what makes the label function $\varrho^{G'}$ well defined (Proposition 17).
--
--   **Formalization Note** The hypothesis $s \ne t$ is the paper's standing assumption on source and sink (§2); without it no flow of positive value exists.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 10, Theorem 13

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem theorem_13 (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a)
    (nu0 l0 : ℝ) (hnu0 : 0 ≤ nu0) (hl0 : 0 ≤ l0) :
    ∃ (x : G.A → ℝ) (l : G.V → ℝ),
      IsStaticFlow G x nu0 ∧ IsThinFlowLabels G Astar ν x l ∧ l G.s = l0 := by sorry

end ThinFlowSP.Breakpoints
