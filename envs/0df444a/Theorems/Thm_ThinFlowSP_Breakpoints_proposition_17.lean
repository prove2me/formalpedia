-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_proposition_17
-- name    : ThinFlowSP.Breakpoints.proposition_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:47.374428+00:00
-- url     : https://prove2.me/theorems/0a0ff87b-eabf-4f7f-8e2e-231c5aa068e3
-- title:
--   Proposition 17, p. 11 — continuous piecewise linear parametric thin flows ϱ^{G′}, χ^{G′} exist
-- statement:
--   Let $G' = (V, A', A^*)$ be a shortest path graph with resetting with $s \ne t$ and $\nu \in \mathbb R^{A'}_{>0}$ capacities. Then there are continuous, piecewise linear functions
--   $$\varrho^{G'} : \mathbb R_{\ge 0} \to \mathbb R^V_{\ge 0}, \qquad \chi^{G'} : \mathbb R_{\ge 0} \to \mathbb R^{A'}_{\ge 0}$$
--   such that for every $\nu'_0 \ge 0$, $\chi^{G'}(\nu'_0)$ is a normalized thin $s$–$t$-flow with resetting of value $\nu'_0$, $\varrho^{G'}(\nu'_0)$ are corresponding labels, and $\varrho^{G'}_s(\nu'_0) = 1$.
--
--   $\varrho^{G'}$ is the object whose breakpoints Theorem 31 counts.
--
--   **Formalization Note** The functions are defined on all of $\mathbb R$; continuity is required on $[0,\infty)$. "Piecewise linear" is encoded as: finitely many breakpoints in $(0, \infty)$, i.e. points around which some component fails to be affine; with continuity this means finitely many affine pieces. The codomains $\mathbb R_{\ge 0}$ follow from the definitions of static flows and labels. The hypothesis $s \ne t$ is the paper's standing assumption on source and sink (§2).
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 11, Proposition 17

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem proposition_17 (G : Net) (Astar : Finset G.A) (ν : G.A → ℝ)
    (hG : IsShortestPathGraph G) (hst : G.s ≠ G.t) (hν : ∀ a, 0 < ν a) :
    ∃ (ρ : ℝ → G.V → ℝ) (χ : ℝ → G.A → ℝ),
      ContinuousOn ρ (Set.Ici 0) ∧ (breakpoints ρ).Finite ∧
      ContinuousOn χ (Set.Ici 0) ∧ (breakpoints χ).Finite ∧
      IsParametricThinFlow G Astar ν ρ χ := by sorry

end ThinFlowSP.Breakpoints
