-- Prove2me | Theorems.Thm_SemialgebraicSDP_Copositive_formPr_one_eq_formP1
-- name    : SemialgebraicSDP.Copositive.formPr_one_eq_formP1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:41.686773+00:00
-- url     : https://prove2.me/theorems/5d1d8bf2-c7b6-4839-87ab-fa1c7896b00b
-- title:
--   §7.5, p. 318 — the case $r = 1$ is the sixth order form $P_1(z) = \sum_{i,j,k} m_{ij} z_i^2 z_j^2 z_k^2$
-- statement:
--   Let $M = (m_{ij})$ be a real symmetric $n \times n$ matrix and $P(z) = \sum_{i,j} m_{ij} z_i^2 z_j^2$. The member $r = 1$ of the family $P_r(z) = (\sum_{i=1}^n z_i^2)^r P(z)$ is the sixth order form displayed on p. 318:
--   $$
--   \Bigl(\sum_{k=1}^n z_k^2\Bigr) P(z) = \sum_{i,j,k} m_{ij} z_i^2 z_j^2 z_k^2 .
--   $$
--
--   This identifies the form whose nonnegativity Theorem 7.7 certifies with the first level of the hierarchy $P_r$.
--
--   **Formalization Note** Both sides are elements of `MvPolynomial (Fin n) ℝ`, and the identity is an equality of polynomials.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 318, §7.5, display defining P_1(z) (case r = 1)

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Forms

namespace SemialgebraicSDP.Copositive

/-- §7.5, p. 318: the case `r = 1` of `P_r` is the sixth order form
`P₁(z) = ∑_{i,j,k} mᵢⱼ zᵢ² zⱼ² z_k²`. -/
theorem formPr_one_eq_formP1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    formPr M 1 = formP1 M := by sorry

end SemialgebraicSDP.Copositive
