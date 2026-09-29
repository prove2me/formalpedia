-- Prove2me | Theorems.Thm_WeierstrassCurve_prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq
-- name    : WeierstrassCurve.prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/db155226-c1d7-595f-832e-faab7ad8c78b
-- title:
--   Generator independence of the half-system x-coordinate polynomial
-- statement:
--   Let $F$ be a field with decidable equality and let $W$ be a Weierstrass curve over $F$ which is elliptic (invertible discriminant). Let $p$ be a prime and $k$ a natural number with $p^k \neq 2$. Let $Q$ and $Q'$ be points of the affine curve $W.\mathrm{toAffine}$, each of exact additive order $p^k$, and suppose that they generate the same subgroup of $\mathbb{Z}$-multiples, $\mathbb{Z}Q = \mathbb{Z}Q'$. For a point $P$ write $(P).\mathrm{coordsOrZero}$ for the pair in $F \times F$ which is $(0,0)$ at the point at infinity and $(x,y)$ at an affine point $(x,y)$, so that its first component is the $x$-coordinate away from infinity. Then the two monic polynomials obtained by running over the "unit half-system" $\{a : 1 \le a \le p^k/2,\ p \nmid a\}$ (integer division) coincide:
--   $$\prod_{1 \le a \le p^k/2,\ p \nmid a} \bigl(X - x(aQ)\bigr) \;=\; \prod_{1 \le a \le p^k/2,\ p \nmid a}\bigl(X - x(aQ')\bigr)$$
--   in $F[X]$, where $x(\cdot)$ denotes the first component of $\mathrm{coordsOrZero}$. For $k = 0$ both products are empty.
--
--   This is the well-definedness statement for the polynomial $\prod (X - x(aQ))$ over a half-system of units modulo $p^k$: it depends only on the cyclic subgroup $\mathbb{Z}Q$ of order $p^k$ and not on the chosen generator, so that such a polynomial is an invariant attached to a cyclic subgroup, i.e. to a $\Gamma_0(p^k)$-structure in generator-kernel form. It is used in the construction of the dictionary between cyclic subgroups of order $p^k$ and kernel polynomials, in particular by [`ModularCurve.forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq`](thm.html#ModularCurve.forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq), [`ModularCurve.IsGamma1Link.exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed`](thm.html#ModularCurve.IsGamma1Link.exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed) and [`ModularCurve.exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed`](thm.html#ModularCurve.exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem WeierstrassCurve.prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ≠ 2)
    (Q Q' : W.toAffine.Point) (hQ : addOrderOf Q = p ^ k) (hQ' : addOrderOf Q' = p ^ k)
    (hQQ' : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C ((a • Q).coordsOrZero).1) =
      ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a), (X - C ((a • Q').coordsOrZero).1) := by sorry
