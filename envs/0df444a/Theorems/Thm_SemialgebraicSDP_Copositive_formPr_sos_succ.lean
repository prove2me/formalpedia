-- Prove2me | Theorems.Thm_SemialgebraicSDP_Copositive_formPr_sos_succ
-- name    : SemialgebraicSDP.Copositive.formPr_sos_succ
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:44.752684+00:00
-- url     : https://prove2.me/theorems/14749fba-bca2-40af-be3c-6d575854a06f
-- title:
--   §7.5, p. 318 — if $P_i$ is a sum of squares, so is $P_{i+1}$
-- statement:
--   Let $M$ be a real symmetric $n \times n$ matrix with associated forms $P_r(z) = (\sum_{i=1}^n z_i^2)^r P(z)$, $r = 0, 1, 2, \dots$, where $P(z) = \sum_{i,j} m_{ij} z_i^2 z_j^2$. For every $i \ge 0$,
--   $$
--   P_i \text{ is a sum of squares} \implies P_{i+1} \text{ is a sum of squares}.
--   $$
--
--   This makes the sum-of-squares tests on $P_0, P_1, P_2, \dots$ a hierarchy of increasingly powerful sufficient conditions for copositivity of $M$.
--
--   **Formalization Note** "Sum of squares" is Mathlib's `IsSumSq` in `MvPolynomial (Fin n) ℝ`.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 318, §7.5 ("if P_i is a sum of squares, then P_{i+1} is also a sum of squares")

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Forms

namespace SemialgebraicSDP.Copositive

/-- §7.5, p. 318: if `P_i` is a sum of squares, then `P_{i+1}` is also a sum of squares. -/
theorem formPr_sos_succ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (i : ℕ)
    (h : IsSumSq (formPr M i)) : IsSumSq (formPr M (i + 1)) := by sorry

end SemialgebraicSDP.Copositive
