-- Prove2me | Theorems.Thm_ShortestGCS_MICP_remark_4_5
-- name    : ShortestGCS.MICP.remark_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:08.731701+00:00
-- url     : https://prove2.me/theorems/fe7c3041-fa77-4d05-af01-d59ca73eb0a3
-- title:
--   Remark 4.5, p. 6 — the perspective function: f̃(x, λ) = λf(x/λ) for λ > 0, f̃ = ∞ for λ < 0, f̃(0, 0) = 0 for proper f
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $f : E \to \mathbb R\cup\{\pm\infty\}$, and $\tilde f$ its perspective (Definition 4.4).
--
--   1. If $\operatorname{epi} f$ is closed, then for every $x$ and every $\lambda > 0$,
--   $$
--   \tilde f(x,\lambda) = \lambda f(x/\lambda).
--   $$
--   2. For every $x$ and every $\lambda < 0$, $\tilde f(x,\lambda) = +\infty$.
--   3. If $f$ is proper, closed and convex, then $\tilde f(0,0) = 0$.
--
--   These three facts are all the paper uses of the perspective function: the cost addend $\tilde\ell_e(z_e,z'_e,y_e)$ of the MICP equals $\ell_e(z_e,z'_e)$ when $y_e = 1$ and vanishes at $(0,0,0)$, the point to which (5.5e) collapses an edge with $y_e = 0$.
--
--   **Formalization Note** Each part carries only the hypothesis it needs (the paper's Definition 4.4 assumes $f$ closed and convex throughout, and its part 3 adds "proper"); the statement is therefore stronger than the page. On $(0, \infty)$, $\lambda f(x/\lambda)$ is computed in `EReal`, where $\lambda\cdot(+\infty) = +\infty$.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, Remark 4.5, p. 6

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun

namespace ShortestGCS.MICP

/-- Remark 4.5, arXiv:2101.11565v5, p. 6: the perspective function `f̃` of Definition 4.4
(i) equals `λ f(x/λ)` for `λ > 0` when `epi f` is closed, (ii) equals `+∞` for `λ < 0`, and
(iii) satisfies `f̃(0, 0) = 0` when `f` is proper, closed and convex. -/
theorem remark_4_5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) :
    (IsClosed (epigraph f) →
        ∀ x : E, ∀ lam : ℝ, 0 < lam → perspectiveFun f x lam = (lam : EReal) * f (lam⁻¹ • x)) ∧
      (∀ x : E, ∀ lam : ℝ, lam < 0 → perspectiveFun f x lam = ⊤) ∧
      (IsProperClosedConvex f → perspectiveFun f 0 0 = 0) := by sorry

end ShortestGCS.MICP
