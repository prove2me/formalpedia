-- Prove2me | Theorems.Thm_WeierstrassCurve_IsTwoKernel_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- name    : WeierstrassCurve.IsTwoKernel.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/6b84ea43-8636-5fe1-ab96-1ada48246d8d
-- title:
--   Unique lifting of Γ₀(2)-kernels along nilpotent thickenings
-- statement:
--   Let $T$ and $T'$ be commutative rings in a common universe and let $\pi \colon T \to T'$ be a surjective ring homomorphism whose kernel is nilpotent, in the sense that $(\ker \pi)^n = 0$ for some natural number $n$. Let $W$ be a Weierstrass curve over $T$ whose discriminant $W.\Delta$ is a unit and for which $2$ is a unit in $T$. Let $h' \in T'[X]$ satisfy the predicate `IsTwoKernel` for the base-changed curve `W.map π`, that is: $h'$ has degree at most $1$, its coefficient in degree $1$ equals $1$, and it divides the $2$-division polynomial $(W.\mathrm{map}\,\pi).\Psi_2^{\mathrm{sq}} = 4X^3 + b_2X^2 + 2b_4X + b_6$ of the base-changed curve. The conclusion asserts that there is exactly one $h \in T[X]$ such that $h$ maps to $h'$ under the coefficientwise map induced by $\pi$ and $h$ satisfies `IsTwoKernel` for $W$, i.e. $h$ has degree at most $1$, coefficient $1$ in degree $1$, and divides $W.\Psi_2^{\mathrm{sq}}$.
--
--   This is the infinitesimal lifting (Hensel) property for $\Gamma_0(2)$-level structures presented in kernel form as monic linear divisors of the $2$-division polynomial, valid when $2$ and the discriminant are invertible, so that the non-trivial $2$-torsion is finite étale. It is used in the proof of [`ModularCurve.IsGamma0PowAt.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot`](thm.html#ModularCurve.IsGamma0PowAt.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot), the corresponding lifting statement for $\Gamma_0$ of a prime power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_IsTwoKernel_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot.lean

import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open ModularCurve

theorem WeierstrassCurve.IsTwoKernel.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (h2 : IsUnit (2 : T))
    (h' : Polynomial T') (hh' : (W.map π).IsTwoKernel h') :
    ∃! h : Polynomial T, h.map π = h' ∧ W.IsTwoKernel h := by sorry
