-- Prove2me | Theorems.Thm_QuadraticForm_exists_ternary_isotropic_mul_of_exists_of_exists
-- name    : QuadraticForm.exists_ternary_isotropic_mul_of_exists_of_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/4f47e726-e10f-5920-913f-47ce889bec7e
-- title:
--   Multiplicativity of isotropy for z²-tx²-uy²
-- statement:
--   Let $K$ be a field and let $t, u, u' \in K$. Assume that the ternary quadratic form $z^2 - t x^2 - u y^2$ is isotropic over $K$, in the sense that there exist $z, x, y \in K$ which are not all three equal to $0$ (the negation of the conjunction $z = 0 \wedge x = 0 \wedge y = 0$) and satisfy $z^2 - t x^2 - u y^2 = 0$; assume likewise that there exist $z, x, y \in K$, not all three zero, with $z^2 - t x^2 - u' y^2 = 0$. The conclusion is that the form with the two coefficients $u$, $u'$ replaced by their product is isotropic in the same sense: there exist $z, x, y \in K$, not all three zero, such that $z^2 - t x^2 - (u u') y^2 = 0$. No restriction is imposed on $t$, $u$, $u'$ (they may vanish), nor on the characteristic of $K$.
--
--   This is the elementary composition step underlying the multiplicativity of the Hilbert symbol $(t,\cdot)$ in its second argument, isotropy of $z^2 - t x^2 - u y^2$ being the condition that $u$ is a norm from $K[\sqrt t]$ up to the usual degenerate cases. It is used in the project to show that the ramification set of a product of quaternion algebras over a fixed quadratic étale algebra behaves as expected, via [`QuaternionAlgebra.isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuadraticForm_exists_ternary_isotropic_mul_of_exists_of_exists.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem QuadraticForm.exists_ternary_isotropic_mul_of_exists_of_exists
    (K : Type) [Field K] (t u u' : K)
    (h : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u * y ^ 2 = 0)
    (h' : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u' * y ^ 2 = 0) :
    ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - (u * u') * y ^ 2 = 0 := by sorry
