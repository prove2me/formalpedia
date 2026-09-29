-- Prove2me | Theorems.Thm_WeierstrassCurve_existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot
-- name    : WeierstrassCurve.existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/fc0d4ab1-2269-565c-9488-1589e8c4e914
-- title:
--   Unique lifting of affine 2-torsion along nilpotent thickenings
-- statement:
--   Let $\pi : T \to T'$ be a surjective homomorphism of commutative rings (both in one universe) whose kernel is nilpotent as an ideal, in the sense that $(\ker \pi)^n = 0$ for some natural number $n$. Let $W$ be a Weierstrass curve over $T$, with coefficients $a_1,\dots,a_6$, and assume that its discriminant $\Delta$ is a unit of $T$ and that the image of $2$ in $T$ is a unit. Let $x', y' \in T'$ be such that the pair $(x',y')$ satisfies the affine Weierstrass equation of the base change $W \otimes_T T'$ obtained by applying $\pi$ to the coefficients, i.e. $y'^2 + a_1' x' y' + a_3' y' = x'^3 + a_2' x'^2 + a_4' x' + a_6'$ with $a_i' = \pi(a_i)$, and in addition satisfy the $2$-division relation $2y' + a_1' x' + a_3' = 0$. The assertion is that there is exactly one pair $(x,y) \in T \times T$ such that $\pi(x) = x'$ and $\pi(y) = y'$, the pair $(x,y)$ satisfies the affine Weierstrass equation of $W$, and $2y + a_1 x + a_3 = 0$.
--
--   This is the Hensel-type lifting property of the non-trivial affine $2$-torsion of a Weierstrass curve: when $2$ and $\Delta$ are invertible, eliminating $y = -(a_1x+a_3)/2$ presents such points as roots of a monic cubic with invertible discriminant, so the locus is finite étale and points lift uniquely along a surjection with nilpotent kernel. It is the $\ell = 2$ case used in the proof of [`WeierstrassCurve.DrinfeldGlobal.existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit`](thm.html#WeierstrassCurve.DrinfeldGlobal.existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit), which lifts level structures along such thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.existsUnique_equation_two_torsion_map_eq_of_surjective_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (h2 : IsUnit ((2 : ℕ) : T))
    (x' y' : T') (hE' : (W.map π).toAffine.Equation x' y') (h2' : 2 * y' + (W.map π).a₁ * x' + (W.map π).a₃ = 0) :
    ∃! P : T × T, (π P.1 = x' ∧ π P.2 = y') ∧ W.toAffine.Equation P.1 P.2 ∧ 2 * P.2 + W.a₁ * P.1 + W.a₃ = 0 := by sorry
