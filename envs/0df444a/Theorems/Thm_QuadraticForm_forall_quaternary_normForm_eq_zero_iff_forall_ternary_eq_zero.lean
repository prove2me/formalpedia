-- Prove2me | Theorems.Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
-- name    : QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/d8422d70-a9ca-5249-9833-e16415e47953
-- title:
--   Anisotropy of a quaternary norm form versus its ternary subform
-- statement:
--   Let $K$ be a field and let $a,b \in K$ be nonzero. The theorem asserts the equivalence of two statements. The first is that the quaternary form $x_0^2 - a x_1^2 - b x_2^2 + ab\,x_3^2$ has only the trivial zero over $K$: for all $x_0,x_1,x_2,x_3 \in K$, if $x_0^2 - a x_1^2 - b x_2^2 + ab\,x_3^2 = 0$ then $x_0 = x_1 = x_2 = x_3 = 0$. The second is the same assertion for the ternary form $z^2 - a x^2 - b y^2$: for all $z,x,y \in K$, if $z^2 - a x^2 - b y^2 = 0$ then $z = x = y = 0$. In other words, the quaternary form, which is the norm form of the quaternion algebra with parameters $a$ and $b$ in the coordinates $x_0, x_1, x_2, x_3$, is anisotropic if and only if its pure ternary subform is anisotropic. The hypotheses $a \neq 0$ and $b \neq 0$ are used only for the implication from the ternary to the quaternary statement.
--
--   This is the classical comparison between a $2$-fold Pfister form and its pure subform: the norm form of a quaternion algebra over $K$ is anisotropic exactly when the associated ternary form is, which is the quadratic-form shape of the criterion for a quaternion algebra to be a division algebra. It is used in the treatment of definite and indefinite quaternion algebras ramified at a prescribed set of places, where the four-variable division-algebra condition must be traded for the three-variable form appearing in Hilbert reciprocity and in local isotropy computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
    (K : Type) [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ↔
      ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0 := by sorry
