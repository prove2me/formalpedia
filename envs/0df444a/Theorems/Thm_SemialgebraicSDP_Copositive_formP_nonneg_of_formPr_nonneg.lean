-- Prove2me | Theorems.Thm_SemialgebraicSDP_Copositive_formP_nonneg_of_formPr_nonneg
-- name    : SemialgebraicSDP.Copositive.formP_nonneg_of_formPr_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:52.572402+00:00
-- url     : https://prove2.me/theorems/0ec31d13-1524-4bd2-bdce-6b8ad0dda1b6
-- title:
--   §7.5, p. 318 — if $P_r(z)$ is nonnegative, then so is $P(z)$
-- statement:
--   Let $M$ be a real symmetric $n \times n$ matrix, $P(z) = \sum_{i,j} m_{ij} z_i^2 z_j^2$ and $P_r(z) = (\sum_{i=1}^n z_i^2)^r P(z)$ for some $r \ge 0$. If $P_r(z) \ge 0$ for every $z \in \mathbb R^n$, then
--   $$
--   P(z) \ge 0 \quad \text{for every } z \in \mathbb R^n .
--   $$
--
--   Together with the equivalence between copositivity of $M$ and nonnegativity of $P$, this shows that a certificate of nonnegativity for any $P_r$ certifies that $M$ is copositive.
--
--   **Formalization Note** Nonnegativity of a polynomial means nonnegativity of its evaluation at every point of $\mathbb R^n$.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 318, §7.5 ("Additionally, if P_r(z) is nonnegative, then so is P(z).")

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Forms

namespace SemialgebraicSDP.Copositive

open MvPolynomial

/-- §7.5, p. 318: if `P_r(z)` is nonnegative, then so is `P(z)`. -/
theorem formP_nonneg_of_formPr_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (r : ℕ) (h : ∀ z : Fin n → ℝ, 0 ≤ eval z (formPr M r)) :
    ∀ z : Fin n → ℝ, 0 ≤ eval z (formP M) := by sorry

end SemialgebraicSDP.Copositive
