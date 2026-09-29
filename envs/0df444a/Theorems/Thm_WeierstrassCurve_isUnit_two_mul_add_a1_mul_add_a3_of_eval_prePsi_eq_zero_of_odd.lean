-- Prove2me | Theorems.Thm_WeierstrassCurve_isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
-- name    : WeierstrassCurve.isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/43219540-161d-5c7d-abc7-9b0a331e03a0
-- title:
--   Unit 2y+a₁x+a₃ at roots of odd division polynomials
-- statement:
--   Let $T$ be a commutative ring and let $W$ be a Weierstrass curve over $T$, with coefficients $a_1,a_2,a_3,a_4,a_6$ and discriminant $\Delta$; assume $\Delta$ is a unit of $T$. Let $\ell$ be a natural number which is odd, and let $x,y \in T$ be such that the affine Weierstrass equation of $W$ holds at $(x,y)$, i.e. $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$, and such that the division polynomial $\mathrm{pre}\Psi_{\ell}$ of $W$ (the polynomial `W.preΨ` evaluated at the integer $\ell$, which for a natural number argument is the one-variable polynomial `W.preΨ' ℓ`) vanishes at $x$: $(\mathrm{pre}\Psi_{\ell})(x) = 0$. The conclusion is that the element $2y + a_1 x + a_3$ of $T$ — the value at $(x,y)$ of the second division polynomial $\psi_2$, equivalently the difference between the $y$-coordinates of $(x,y)$ and of its negative — is a unit of $T$. No hypothesis of invertibility of $2$, nor any restriction on $T$ beyond commutativity and the invertibility of $\Delta$, is imposed.
--
--   The statement says that a point whose $x$-coordinate is annihilated by an odd division polynomial is nowhere on $\operatorname{Spec} T$ a $2$-torsion point, in the strong form that $\psi_2$ takes a unit value; this invertibility is what allows a variable change to be performed. It is used in the construction of normalised Weierstrass models carrying level structures, being cited by [`ModularCurve.LevelP.exists_levelPData_map_eq_relabel_univData`](thm.html#ModularCurve.LevelP.exists_levelPData_map_eq_relabel_univData) and by [`WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range`](thm.html#WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
    {T : Type*} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    {ℓ : ℕ} (hℓ : Odd ℓ) {x y : T} (heq : W.toAffine.Equation x y) (hℓx : (W.preΨ ℓ).eval x = 0) :
    IsUnit (2 * y + W.a₁ * x + W.a₃) := by sorry
