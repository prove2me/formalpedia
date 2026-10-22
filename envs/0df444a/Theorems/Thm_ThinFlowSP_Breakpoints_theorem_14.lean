-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_theorem_14
-- name    : ThinFlowSP.Breakpoints.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:39.085064+00:00
-- url     : https://prove2.me/theorems/b16ca11e-b884-47ce-a1d7-d99e3f5a0b28
-- title:
--   Theorem 14, p. 10 — labels are monotone in the flow value and in the label at s
-- statement:
--   Let $G' = (V, A', A^*)$ be a shortest path graph with resetting with $s \ne t$ and $\nu \in \mathbb R^{A'}_{>0}$ capacities. Let $x'$, $\hat x'$ be normalized thin $s$–$t$-flows with resetting with values $|x'|$, $|\hat x'|$ and corresponding labels $\ell'$, $\hat\ell'$. If
--   $$|x'| \le |\hat x'| \quad\text{and}\quad \ell'_s \le \hat\ell'_s,$$
--   then $\ell'_v \le \hat\ell'_v$ for every vertex $v$.
--
--   Monotonicity yields uniqueness of the labels (Corollary 15) and the monotonicity properties of $\varrho^{G'}$ (Lemma 18).
--
--   **Formalization Note** The hypothesis $s \ne t$ is the paper's standing assumption on source and sink (§2).
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 10, Theorem 14

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem theorem_14 (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a)
    (x xh : G.A → ℝ) (l lh : G.V → ℝ) (val valh : ℝ)
    (hx : IsStaticFlow G x val) (hxh : IsStaticFlow G xh valh)
    (hl : IsThinFlowLabels G Astar ν x l) (hlh : IsThinFlowLabels G Astar ν xh lh)
    (hval : val ≤ valh) (hs : l G.s ≤ lh G.s) :
    ∀ v, l v ≤ lh v := by sorry

end ThinFlowSP.Breakpoints
