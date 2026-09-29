-- Prove2me | Theorems.Thm_PeriodPair_exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet
-- name    : PeriodPair.exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e5bd0a58-504a-5f94-b76a-176d47adf676
-- title:
--   Rational homomorphisms of lattice curves lift to z ↦ az
-- statement:
--   Let $L$ and $L'$ be period pairs, with associated Weierstrass curves over $\mathbb{C}$ given by [`PeriodPair.weierstrassCurve`](def/PeriodPair_Uniformization.html#L13), namely $y^2 = x^3 - (g_2/4)x - (g_3/4)$ with the invariants $g_2, g_3$ of the respective pair, and assume $hL$ and $hL'$: the quantities $g_2^3 - 27g_3^2$ of $L$ and of $L'$ are non-zero (a condition that in fact always holds, by [`PeriodPair.discriminant_ne_zero`](thm.html#PeriodPair.discriminant_ne_zero)). Let $\alpha$ be an additive group homomorphism from the group of affine points of $L$'s curve to that of $L'$'s curve, and assume $\alpha$ lies in [`WeierstrassCurve.rationalHomSet ℂ`](def/WeierstrassCurve_RationalEnd.html#L28), that is: either $\alpha = 0$, or there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ with complex coefficients and a finite set $B \subseteq \mathbb{C}$ such that for every nonsingular affine point $(x,y)$ of $L$'s curve with $x \notin B$ one has $d_X(x,y) \neq 0$, $d_Y(x,y) \neq 0$ and $\alpha$ sends $(x,y)$ to the affine point $\bigl(n_X(x,y)/d_X(x,y),\, n_Y(x,y)/d_Y(x,y)\bigr)$. The conclusion is that there exists $a \in \mathbb{C}$ with $\alpha(\pi_L(z)) = \pi_{L'}(az)$ for all $z \in \mathbb{C}$, where $\pi_L =$ `L.toPoint hL` is the Weierstrass parametrisation of $L$: it sends $z$ in the lattice of $L$ to the point at infinity, and otherwise to the nonsingular affine point with coordinates the Weierstrass $\wp$-data of $L$ at $z$, and likewise for $\pi_{L'}$.
--
--   This is the injectivity-and-linearity half of the classical analytic dictionary $\mathrm{Hom}(E_\Lambda, E_{\Lambda'}) \cong \{a \in \mathbb{C} : a\Lambda \subseteq \Lambda'\}$: a homomorphism of complex lattice curves that is rational in the above sense lifts through the uniformisations to multiplication by a single scalar on the universal covers. It is used in the construction of non-trivial elements of [`WeierstrassCurve.rationalHomSet`](def/WeierstrassCurve_RationalEnd.html#L28), via [`WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul`](thm.html#WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PeriodPair.exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) {α : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet ℂ L.weierstrassCurve L'.weierstrassCurve) : ∃ a : ℂ, ∀ z : ℂ, α (L.toPoint hL z) = L'.toPoint hL' (a * z) := by sorry
