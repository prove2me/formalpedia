-- Prove2me | Theorems.Thm_WeierstrassCurve_rootMultiplicity_hasseInvariant_jFamily_eq_one
-- name    : WeierstrassCurve.rootMultiplicity_hasseInvariant_jFamily_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/5659f851-a02e-56ff-bed7-dc4613f252d7
-- title:
--   Supersingular parameters are simple roots of the Hasse polynomial
-- statement:
--   Let $q \ge 5$ be a prime and let $k$ be an algebraically closed field of characteristic $q$. Consider the one-parameter Weierstrass curve over the polynomial ring $k[X]$ with coefficients $a_1 = 1$, $a_2 = 0$, $a_3 = 0$, $a_4 = -36X$, $a_6 = -X$, that is $y^2 + xy = x^3 - 36Xx - X$, and its Hasse invariant $\mathrm{hasseInvariant}\ q$, the coefficient of degree $q-1$ in the $((q-1)/2)$-th power of the two-torsion polynomial of the curve, which is an element of $k[X]$. Let $a \in k$ satisfy $a \ne 0$ and $a \ne 1728$, and assume $a \in$ `ssJSet q k`, i.e. every Weierstrass curve $W$ over $k$ which is elliptic and has $j$-invariant $W.j = a$ has the property that every point $P$ of its affine model with $q \cdot P = 0$ is the zero point. Then the root multiplicity of $(a - 1728)^{-1}$ in that polynomial $\mathrm{hasseInvariant}\ q$ of $k[X]$ equals $1$.
--
--   The family $y^2 + xy = x^3 - 36tx - t$ has $j$-invariant $t^{-1} + 1728$, so $t_a = (a-1728)^{-1}$ is the parameter value carrying $j$-invariant $a$; the statement is the classical simplicity (Deuring, Igusa) of the supersingular roots of the Hasse polynomial, here in the $j$-line coordinate rather than in the Legendre parameter $\lambda$, and restricted to supersingular $a \notin \{0, 1728\}$ and to primes $q \ge 5$. It is used in the analysis of [`WeierstrassCurve.hasseInvariant_jFamily`](thm.html#WeierstrassCurve.hasseInvariant_jFamily), where the Hasse polynomial of this family is identified through its roots and their multiplicities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_rootMultiplicity_hasseInvariant_jFamily_eq_one.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.rootMultiplicity_hasseInvariant_jFamily_eq_one
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet q k) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    Polynomial.rootMultiplicity (a - 1728)⁻¹ (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))) = 1 := by sorry
