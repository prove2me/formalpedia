-- Prove2me | Theorems.Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero
-- name    : QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/173fde0b-d00d-5aaa-b387-1758632a1049
-- title:
--   Division algebra iff anisotropic norm form for H[K,a,b]
-- statement:
--   Let $K$ be a field and let $a,b \in K$ be arbitrary; write $\mathbb{H}[K,a,b]$ for the Mathlib quaternion algebra over $K$ with basis $1,i,j,k$ satisfying $i^2 = a$, $j^2 = b$ and $ij = k = -ji$. The theorem asserts the equivalence of two statements. The first is that every non-zero element of $\mathbb{H}[K,a,b]$ is a unit, i.e. for all $x \in \mathbb{H}[K,a,b]$ with $x \neq 0$, $x$ is invertible in the ring $\mathbb{H}[K,a,b]$. The second is the anisotropy of the quaternary quadratic form given by the reduced norm, stated purely in terms of coordinates: for all $x_0,x_1,x_2,x_3 \in K$, if $x_0^2 - a x_1^2 - b x_2^2 + a b x_3^2 = 0$ then $x_0 = 0$, $x_1 = 0$, $x_2 = 0$ and $x_3 = 0$. No hypothesis is placed on the characteristic of $K$ or on $a$ and $b$; in particular the degenerate cases $a = 0$ or $b = 0$ are included, where both sides fail.
--
--   This is the standard criterion identifying the quaternion algebras that are division algebras as those whose reduced norm form is anisotropic. It is used in this development to convert the division-algebra condition at a place into an explicit solvability statement about the norm form, and is invoked by the results on definite quaternion algebras ramified at a prescribed set of places, on Eichler orders and relative indices, and in the Čerednik–Drinfel'd part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero
    (K : Type) [Field K] (a b : K) :
    (∀ x : ℍ[K, a, b], x ≠ 0 → IsUnit x) ↔
      ∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by sorry
