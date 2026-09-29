-- Prove2me | Theorems.Thm_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_sq_eq_bot
-- name    : WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_sq_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/98e9bb7a-eb24-5c75-9f72-b0f273d27f24
-- title:
--   No infinitesimal automorphisms of an elliptic Weierstrass equation
-- statement:
--   Let $T$ be a commutative ring and let $W$ be a Weierstrass curve over $T$, that is, a tuple of coefficients $a_1,a_2,a_3,a_4,a_6$ presenting the equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$. Assume that the discriminant $W.\Delta$ is a unit of $T$. Let $I$ be an ideal of $T$ with $I^2 = \bot$, i.e. $I$ is square-zero. Let $C$ be an admissible change of Weierstrass variables over $T$, given by a unit $C.u \in T^\times$ and elements $C.r, C.s, C.t \in T$, acting on Weierstrass coefficients through $x = u^2x' + r$, $y = u^3y' + u^2sx' + t$. Assume that $C$ is congruent to the identity modulo $I$, in the sense that $(C.u : T) - 1 \in I$ and $C.r, C.s, C.t \in I$, and that $C$ fixes $W$ under this action, $C \bullet W = W$. Then $C$ is the identity change of variables $1$, i.e. $C.u = 1$ and $C.r = C.s = C.t = 0$.
--
--   This is the infinitesimal rigidity of an elliptic Weierstrass equation: the automorphism group scheme of a Weierstrass curve with unit discriminant, together with its origin, is unramified, so a change of variables trivial modulo a square-zero ideal and fixing the equation is already trivial. It is used in the uniqueness half of the lifting of Weierstrass models, being cited by [`WeierstrassCurve.VariableChange.eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing`](thm.html#WeierstrassCurve.VariableChange.eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing) and by [`WeierstrassCurve.exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne`](thm.html#WeierstrassCurve.exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_sq_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_sq_eq_bot
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (I : Ideal T) (hI : I ^ 2 = ⊥) (C : WeierstrassCurve.VariableChange T)
    (hu : (C.u : T) - 1 ∈ I) (hr : C.r ∈ I) (hs : C.s ∈ I) (ht : C.t ∈ I)
    (hC : C • W = W) : C = 1 := by sorry
