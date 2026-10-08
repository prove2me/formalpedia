-- Prove2me | Theorems.Thm_ReluMIP_Ideal_relax6_eq_convexHull
-- name    : ReluMIP.Ideal.relax6_eq_convexHull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:17.875419+00:00
-- url     : https://prove2.me/theorems/54526288-560b-45b0-9c34-b1dd71de2247
-- title:
--   App. A.1, p. 14 — the LP relaxation of (6) is the convex hull of its points with z ∈ {0, 1}
-- statement:
--   Let $f(x)=w\cdot x+b$ and $L,U\in\mathbb R^\eta$ with $L_i<U_i$ for every $i$. Let $R_6$ be the LP relaxation of formulation (6): the points $(x,y,z)\in[L,U]\times\mathbb R_{\ge0}\times[0,1]$ with $y\ge w\cdot x+b$ and, for every $I\subseteq\operatorname{supp}(w)$,
--   $$
--   y\le\sum_{i\in I}w_i\bigl(x_i-\breve L_i(1-z)\bigr)+\Bigl(b+\sum_{i\notin I}w_i\breve U_i\Bigr)z .
--   $$
--   Then
--   $$
--   R_6=\operatorname{conv}\{(x,y,z)\in R_6 : z\in\{0,1\}\}.
--   $$
--
--   This is the content of the first sentence of Appendix A.1: $R_6$ is the projection of the ideal extended formulation (5), so it inherits its integrality. Proposition 1 follows from it.
--
--   **Formalization Note** Strict activity is not assumed (the identity holds without it).
-- source:
--   arXiv:1811.08359v2, App. A.1, first sentence, p. 14

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting

namespace ReluMIP.Ideal

/-- App. A.1, p. 14 (arXiv:1811.08359v2): the LP relaxation of (6) is the projection of the ideal
extended formulation (5), hence equals the convex hull of its points with `z ∈ {0, 1}`. -/
theorem relax6_eq_convexHull {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) :
    relax6 w b L U = convexHull ℝ {p | p ∈ relax6 w b L U ∧ (p.2.2 = 0 ∨ p.2.2 = 1)} := by sorry

end ReluMIP.Ideal
