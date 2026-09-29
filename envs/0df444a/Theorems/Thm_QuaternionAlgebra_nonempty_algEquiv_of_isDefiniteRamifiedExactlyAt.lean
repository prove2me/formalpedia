-- Prove2me | Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/4485a022-e37e-5885-bc55-7ef283578301
-- title:
--   Uniqueness of definite rational quaternion algebras ramified exactly at q
-- statement:
--   Let $q$ be a prime number and let $a,b,c,d$ be rational numbers. Assume that the pair $(a,b)$ satisfies the predicate `IsDefiniteRamifiedExactlyAt` at $q$, that is: $a<0$, $b<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the condition that every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ (the quaternion algebra with $i^2=a$, $j^2=b$, $ij=-ji$, base changed to the $v$-adic completion of $\mathbb{Q}$) is a unit holds if and only if $q$ lies in the prime ideal $v$; and assume the same three conditions for the pair $(c,d)$, with the same $q$. The conclusion is that the type of $\mathbb{Q}$-algebra isomorphisms $\mathbb{H}[\mathbb{Q},a,b]\simeq_{\mathbb{Q}}\mathbb{H}[\mathbb{Q},c,d]$ is nonempty, i.e. the two quaternion algebras $\left(\frac{a,b}{\mathbb{Q}}\right)$ and $\left(\frac{c,d}{\mathbb{Q}}\right)$ are isomorphic as algebras over $\mathbb{Q}$. Note that the negativity conditions $a<0$, $b<0$ stand in for definiteness at the real place, and that the division-algebra condition at a finite place is expressed as invertibility of all nonzero elements of the completed algebra.
--
--   This is the uniqueness half of the classification of quaternion algebras over $\mathbb{Q}$ by their set of ramified places, specialised to the ramification set $\{q,\infty\}$: a definite rational quaternion algebra of prime discriminant $q$ is determined up to isomorphism. It serves to identify a quaternion algebra arising abstractly with a chosen presentation $\mathbb{H}[\mathbb{Q},c,d]$, and is used in the construction of Eichler orders and their matrix descriptions in the indefinite ramified-exactly-at-$q$ setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.nonempty_algEquiv_of_isDefiniteRamifiedExactlyAt
    {q : ℕ} [Fact q.Prime] {a b c d : ℚ}
    (h₁ : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    (h₂ : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt c d q) :
    Nonempty (ℍ[ℚ, a, b] ≃ₐ[ℚ] ℍ[ℚ, c, d]) := by sorry
