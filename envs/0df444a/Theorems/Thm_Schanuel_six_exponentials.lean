-- Prove2me | Theorems.Thm_Schanuel_six_exponentials
-- name    : Schanuel.six_exponentials
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T17:33:29.019026+00:00
-- url     : https://prove2.me/theorems/75ca528d-83e0-43c7-b183-42e42df38b0f
-- title:
--   Six exponentials theorem
-- statement:
--   **Six exponentials theorem.** Let $x_1, x_2$ be complex numbers that are linearly independent over $\mathbb{Q}$, and let $y_1, y_2, y_3$ be complex numbers that are linearly independent over $\mathbb{Q}$. Then at least one of the six numbers $$e^{x_i y_j}, \qquad i \in \{1,2\},\ j \in \{1,2,3\},$$ is transcendental.
--
--   Equivalently: the six numbers cannot all be algebraic. The theorem is due to Siegel (unpublished), Lang and Ramachandra. The analogous statement with two $x$'s and two $y$'s — the four exponentials conjecture — is open, and follows from Schanuel's conjecture.
-- source:
--   S. Lang, Introduction to Transcendental Numbers, Addison-Wesley, 1966, Chapter II; K. Ramachandra, Contributions to the theory of transcendental numbers I, Acta Arith. 14 (1968), 65–72

import Mathlib

namespace Schanuel
theorem six_exponentials (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) := by sorry
end Schanuel
