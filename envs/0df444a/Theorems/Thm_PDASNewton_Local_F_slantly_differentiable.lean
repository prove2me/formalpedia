-- Prove2me | Theorems.Thm_PDASNewton_Local_F_slantly_differentiable
-- name    : PDASNewton.Local.F_slantly_differentiable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:32.80467+00:00
-- url     : https://prove2.me/theorems/aae1867e-2400-44d2-b8fe-11f0833a9273
-- title:
--   §3, p. 7 — F is slantly differentiable on ℝⁿ × ℝⁿ with slanting function G_F, the system matrix of (2.4)
-- statement:
--   Let $A \in \mathbb{R}^{n \times n}$, $f, \psi \in \mathbb{R}^n$ and $c > 0$, and let
--   $$F(y, \lambda) = \bigl(Ay + \lambda - f,\ \lambda - \max(0, \lambda + c(y - \psi))\bigr).$$
--   Then $F$ is slantly differentiable on $\mathbb{R}^n \times \mathbb{R}^n$ and the system matrix $G_F$ of (2.4), built from $G_m$ with $\delta = 0$, is a slanting function for $F$: for every $x \in \mathbb{R}^n \times \mathbb{R}^n$,
--   $$\lim_{h \to 0} \frac{1}{\|h\|}\,\|F(x+h) - F(x) - G_F(x+h)h\| = 0.$$
--
--   This is the hypothesis of Theorem 1.1 that the paper derives from Lemma 3.1.
--
--   **Formalization Note** No matrix hypothesis is needed; $c > 0$ is the paper's standing assumption. Pairs carry the product of sup norms.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 7, paragraph after the definition of F

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting

namespace PDASNewton.Local

/-- §3, p. 7: as a consequence of Lemma 3.1, `F` is slantly differentiable on `ℝⁿ × ℝⁿ` and the
system matrix `G_F` of (2.4) is a slanting function for `F`. -/
theorem F_slantly_differentiable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ)
    (c : ℝ) (hc : 0 < c) :
    IsSlantingFunction (Fmap A f ψ c) (GF A ψ c) Set.univ := by sorry

end PDASNewton.Local
