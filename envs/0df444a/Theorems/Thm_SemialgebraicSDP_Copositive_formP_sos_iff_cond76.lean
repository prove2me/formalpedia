-- Prove2me | Theorems.Thm_SemialgebraicSDP_Copositive_formP_sos_iff_cond76
-- name    : SemialgebraicSDP.Copositive.formP_sos_iff_cond76
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:47.031306+00:00
-- url     : https://prove2.me/theorems/61edb6dd-2f0f-461b-95cc-c8c15c8c85b8
-- title:
--   §7.5, p. 317 — $P(z)$ is a sum of squares if and only if $M = P + N$ with $P \succeq 0$, $n_{ij} \ge 0$ (7.6)
-- statement:
--   Let $M = (m_{ij})$ be a real symmetric $n \times n$ matrix and let
--   $$
--   P(z) = \sum_{i,j} m_{ij} z_i^2 z_j^2
--   $$
--   be the associated fourth order form in the real variables $z_1, \dots, z_n$. Then $P(z)$ is a sum of squares of real polynomials if and only if condition (7.6) holds: $M = P + N$ for a positive semidefinite matrix $P$ and a matrix $N = (n_{ij})$ with $n_{ij} \ge 0$ for all $i, j$.
--
--   This is the paper's observation that the sum-of-squares sufficient condition for the nonnegativity of $P(z)$, applied to copositivity, is equivalent to the classical sufficient condition (7.6) (the paper also credits [CL77, Lemma 3.5]). It places (7.6) at level $0$ of the hierarchy of sum-of-squares tests for copositivity.
--
--   **Formalization Note** "Sum of squares" is Mathlib's `IsSumSq` in the polynomial ring `MvPolynomial (Fin n) ℝ`: a finite sum of squares of polynomials. Both directions of the page's "equivalent" are stated. `Cond76 M` does not require $N$ symmetric (the page does not); with $M$ symmetric and $P$ positive semidefinite it is forced.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 317, §7.5, sentence before and display (7.6)

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Forms
import Definitions.Def_SemialgebraicSDP_Copositive_Certificates

namespace SemialgebraicSDP.Copositive

/-- §7.5, p. 317: for a symmetric `M`, the form `P(z)` is a sum of squares of polynomials if and
only if `M` decomposes as `M = P + N` with `P ⪰ 0` and `N` elementwise nonnegative (7.6). -/
theorem formP_sos_iff_cond76 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    IsSumSq (formP M) ↔ Cond76 M := by sorry

end SemialgebraicSDP.Copositive
