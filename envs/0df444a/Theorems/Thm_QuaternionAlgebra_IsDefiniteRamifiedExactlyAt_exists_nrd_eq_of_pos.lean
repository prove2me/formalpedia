-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_nrd_eq_of_pos
-- name    : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_nrd_eq_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/d823ade8-ba7e-5e9d-a569-51d63193fc71
-- title:
--   Positive rationals are reduced norms on a definite quaternion algebra
-- statement:
--   Let $a,b$ be rational numbers and let $q$ be a prime number with $q \neq 2$. Assume that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is definite and ramified exactly at $q$ in the sense of the project predicate [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt`](def/QuaternionAlgebra_EichlerOrder.html#L87), namely: $a < 0$, $b < 0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ (the tensor product with the $v$-adic completion) has the property that each of its nonzero elements is a unit if and only if $q$, viewed in the ring of integers, lies in the prime ideal attached to $v$. Let $t$ be a rational number with $0 < t$. Then there exists $\gamma \in \mathbb{H}[\mathbb{Q},a,b]$ whose reduced norm equals $t$, where the reduced norm of a quaternion $x$ is the rational number $x_{\mathrm{re}}^2 - a\,x_{\mathrm{imI}}^2 - b\,x_{\mathrm{imJ}}^2 + ab\,x_{\mathrm{imK}}^2$. Note that the conclusion only asserts the existence of a quaternion of reduced norm $t$; being of nonzero reduced norm, such a $\gamma$ is automatically invertible.
--
--   This is the Hasse–Schilling–Maass norm theorem (Eichler's norm theorem) in the case of a definite quaternion algebra over $\mathbb{Q}$ of odd prime discriminant: the reduced norms of invertible elements are exactly the positive rationals. It is used in the Čerednik–Drinfel'd part of the development, where elements and units of prescribed reduced norm are produced in orders and localisations of $\mathbb{H}[\mathbb{Q},a,b]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_nrd_eq_of_pos.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_nrd_eq_of_pos
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hq : q ≠ 2)
    (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    (t : ℚ) (ht : 0 < t) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = t := by sorry
