-- Prove2me | Theorems.Thm_SolodovSvaiterVI_Alg21_eq2_5_inner_residual_ge
-- name    : SolodovSvaiterVI.Alg21.eq2_5_inner_residual_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T10:26:20.304806+00:00
-- url     : https://prove2.me/theorems/45c2cafb-50e4-48de-8890-fb2b75a00e6e
-- title:
--   Eq. (2.5): $\langle F(x), r(x) \rangle \ge \|r(x)\|^2$ for $x \in C$
-- statement:
--   Let $C$ be a closed convex subset of $\mathbb{R}^n$, $F : \mathbb{R}^n \to \mathbb{R}^n$, and $r(x) = x - P_C[x - F(x)]$ the projected residual. For every $x \in C$,
--
--   $$\langle F(x), r(x) \rangle \ge \|r(x)\|^2. \tag{2.5}$$
--
--   Inequality (2.5) says that $-r(x)$ is a direction along which $F(x)$ has a definite component; it is what makes the linesearch of Algorithm 2.1 terminate and what identifies limit points as solutions.
--
--   **Formalization Note** $C$ is nonempty because $x \in C$. $P_C$ is `projOnto C`.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 769, proof of Theorem 2.1, Eq. (2.5)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_residual

open scoped InnerProductSpace

namespace SolodovSvaiterVI.Alg21

/-- Solodov–Svaiter, proof of Theorem 2.1, (2.5) (p. 769): for `x ∈ C` with `C` closed and
convex, `⟨F(x), r(x)⟩ ≥ ‖r(x)‖²`. -/
theorem eq2_5_inner_residual_ge {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCc : IsClosed C) (hCcv : Convex ℝ C)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ C) :
    ‖residual F C x‖ ^ 2 ≤ ⟪F x, residual F C x⟫_ℝ := by sorry

end SolodovSvaiterVI.Alg21
