-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal
-- name    : WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/63f44064-7685-5977-a8ae-4a9d32227253
-- title:
--   Uniqueness of the origin-chart solution v over a local ring
-- statement:
--   Let $S$ be a commutative local ring with maximal ideal $\mathfrak{m} =$ `maximalIdeal S`, and let $a_1, a_2, a_3, a_4, a_6, x, v, v'$ be elements of $S$. Assume that $x$, $v$ and $v'$ all lie in $\mathfrak{m}$, and that both $v$ and $v'$ satisfy the inhomogeneous Weierstrass relation in the chart at the origin with the same $x$, namely $$v + a_1 x v + a_3 v^2 = x^3 + a_2 x^2 v + a_4 x v^2 + a_6 v^3$$ and the same identity with $v'$ in place of $v$. The conclusion is that $v = v'$. Thus, for fixed coefficients $a_1,\dots,a_6$ and fixed $x \in \mathfrak{m}$, there is at most one $v \in \mathfrak{m}$ solving this cubic relation. No completeness or separatedness assumption on $S$ is imposed; only that $S$ is local.
--
--   This is the uniqueness half of the standard construction of the formal group of a Weierstrass curve at the origin, where the affine chart $(x,v)$ with $x = X/Z$, $v = Y/Z$ replaced by the coordinates adapted to $O$ makes $v$ a power series in $x$ with coefficients determined by the $a_i$. It is used in the Drinfeld-style global analysis of Weierstrass models, in [`WeierstrassCurve.DrinfeldGlobal.mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow`](thm.html#WeierstrassCurve.DrinfeldGlobal.mem_comap_maximalIdeal_pow_of_map_mem_maximalIdeal_pow) and in [`WeierstrassProjModel.coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq`](thm.html#WeierstrassProjModel.coeff_laurent_zChart_of_iso_of_kwZeroSect_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_mem_maximalIdeal
    {S : Type u} [CommRing S] [IsLocalRing S] (a₁ a₂ a₃ a₄ a₆ x v v' : S)
    (hx : x ∈ maximalIdeal S) (hv : v ∈ maximalIdeal S) (hv' : v' ∈ maximalIdeal S)
    (h : v + a₁ * x * v + a₃ * v ^ 2 = x ^ 3 + a₂ * x ^ 2 * v + a₄ * x * v ^ 2 + a₆ * v ^ 3)
    (h' : v' + a₁ * x * v' + a₃ * v' ^ 2 = x ^ 3 + a₂ * x ^ 2 * v' + a₄ * x * v' ^ 2 + a₆ * v' ^ 3) :
    v = v' := by sorry
