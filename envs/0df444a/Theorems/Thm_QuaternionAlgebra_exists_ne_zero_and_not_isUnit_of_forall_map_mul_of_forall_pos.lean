-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_ne_zero_and_not_isUnit_of_forall_map_mul_of_forall_pos
-- name    : QuaternionAlgebra.exists_ne_zero_and_not_isUnit_of_forall_map_mul_of_forall_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/bfc779a4-bc31-5bcd-8afe-de610da60362
-- title:
--   No multiplicative positive form on an indefinite rational quaternion algebra
-- statement:
--   Let $a$ and $b$ be rational numbers with $0 < a$ or $0 < b$, and let $\mathbb{H}[\mathbb{Q}, a, b]$ be the rational quaternion algebra with basis $1, i, j, k$ subject to $i^2 = a$, $j^2 = b$, $ij = -ji = k$. Suppose $Q$ is a $\mathbb{Q}$-valued quadratic map on $\mathbb{H}[\mathbb{Q}, a, b]$ (in the sense of Mathlib's `QuadraticMap`) which is multiplicative, $Q(xy) = Q(x)Q(y)$ for all $x, y$, and positive on non-zero elements, $Q(x) > 0$ whenever $x \neq 0$. The conclusion is that there exists $x \in \mathbb{H}[\mathbb{Q}, a, b]$ with $x \neq 0$ and $x$ not a unit; that is, the algebra is not a division algebra. Note that the hypothesis $0 < a \vee 0 < b$ is used only to produce one generator with positive square, and that no separate hypothesis asserts that the algebra is a division algebra — the statement is the contrapositive form, producing a non-zero non-unit outright.
--
--   This is the quadratic-form half of the classical fact that a multiplicative positive definite form can live only on a definite quaternion algebra (a composition-algebra phenomenon): an indefinite rational quaternion algebra carries no multiplicative positive definite quadratic form. It is used in the construction of fake elliptic curves for the Čerednik–Drinfel'd setting, where positivity of a degree form on an endomorphism algebra forces the algebra to be definite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_ne_zero_and_not_isUnit_of_forall_map_mul_of_forall_pos.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_ne_zero_and_not_isUnit_of_forall_map_mul_of_forall_pos
    {a b : ℚ} (hab : 0 < a ∨ 0 < b) (Q : QuadraticMap ℚ ℍ[ℚ, a, b] ℚ)
    (hmul : ∀ x y : ℍ[ℚ, a, b], Q (x * y) = Q x * Q y) (hpos : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → 0 < Q x) :
    ∃ x : ℍ[ℚ, a, b], x ≠ 0 ∧ ¬ IsUnit x := by sorry
