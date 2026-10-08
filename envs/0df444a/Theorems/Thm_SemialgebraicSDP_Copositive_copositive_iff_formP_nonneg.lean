-- Prove2me | Theorems.Thm_SemialgebraicSDP_Copositive_copositive_iff_formP_nonneg
-- name    : SemialgebraicSDP.Copositive.copositive_iff_formP_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:37.18523+00:00
-- url     : https://prove2.me/theorems/2b9ca530-ebb7-4c2e-ac0a-e250a8fd3064
-- title:
--   §7.5, p. 317 — $M$ is copositive iff the form $P(z)$ is positive semidefinite
-- statement:
--   Let $M = (m_{ij})$ be a real symmetric $n \times n$ matrix. Recall that $M$ is **copositive** if $x^T M x \ge 0$ for every $x \in \mathbb R^n$ with $x_i \ge 0$ for all $i$, and let $P(z) = \sum_{i,j} m_{ij} z_i^2 z_j^2$ be the associated fourth order form. Then
--   $$
--   M \text{ is copositive} \iff P(z) \ge 0 \text{ for all } z \in \mathbb R^n .
--   $$
--
--   This reduces copositivity, a condition on the nonnegative orthant, to global nonnegativity (positive semidefiniteness) of a form, so that any sufficient condition for nonnegativity of $P$, such as a sum-of-squares certificate, becomes a sufficient condition for copositivity.
--
--   **Formalization Note** A form is called positive semidefinite in the paper when it is nonnegative at every real point; this is stated directly as nonnegativity of the evaluation. Copositivity is the published definition `MurtyKabadi.Reduction.Copositive`.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 317, §7.5 ("It is easy to verify that M is copositive if and only if the form P(z) is positive semidefinite.")

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_SemialgebraicSDP_Copositive_Forms

namespace SemialgebraicSDP.Copositive

open MvPolynomial

/-- §7.5, p. 317: a symmetric matrix `M` is copositive if and only if the form `P(z)` is
positive semidefinite, i.e. nonnegative at every real point. -/
theorem copositive_iff_formP_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    MurtyKabadi.Reduction.Copositive M ↔ ∀ z : Fin n → ℝ, 0 ≤ eval z (formP M) := by sorry

end SemialgebraicSDP.Copositive
