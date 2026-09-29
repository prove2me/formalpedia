-- Prove2me | Theorems.Thm_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
-- name    : WeierstrassCurve.hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/85657090-d2f9-5283-805f-fba3260c08bc
-- title:
--   Hasse¹²Δ^{-(q-1)} is an invariant of j
-- statement:
--   Let $q$ be a prime and let $F$ be a separably closed field of characteristic $q$. Let $W$ and $W'$ be Weierstrass curves over $F$, both elliptic (so that each has invertible discriminant), and suppose their $j$-invariants agree, $j(W) = j(W')$. Here the Hasse invariant $\mathrm{hasseInvariant}\ q\ W$ of a Weierstrass curve $W$ over a commutative ring is defined as the coefficient of the monomial of degree $q-1$ in the $((q-1)/2)$-th power of the polynomial underlying the two-torsion polynomial of $W$ (the cubic whose roots are the $x$-coordinates of the $2$-torsion). The conclusion is the identity in $F$
--   $$\mathrm{hasseInvariant}\ q\ W^{12}\cdot \Delta(W')^{\,q-1} \;=\; \mathrm{hasseInvariant}\ q\ W'^{12}\cdot \Delta(W)^{\,q-1},$$
--   where $\Delta$ denotes the discriminant of a Weierstrass curve. Thus the ratio $\mathrm{hasseInvariant}^{12}/\Delta^{q-1}$, which is well defined because the discriminants are units, depends only on the $j$-invariant.
--
--   The quantity $\mathrm{Hasse}^{12}/\Delta^{q-1}$ is the weight-normalised form of the Hasse invariant, i.e. the invariant whose vanishing detects supersingularity; the statement records that it is an isomorphism invariant, hence a function of $j$ alone over a separably closed field. It is used to transport the computation of the invariant to an explicit Weierstrass family parametrised by $j$, and is cited in the construction of the Deuring/supersingular polynomial and in the identification of the supersingular $j$-set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
    (q : ℕ) [Fact q.Prime]
    {F : Type*} [Field F] [CharP F q] [IsSepClosed F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (h : W.j = W'.j) :
    WeierstrassCurve.hasseInvariant q W ^ 12 * W'.Δ ^ (q - 1) =
      WeierstrassCurve.hasseInvariant q W' ^ 12 * W.Δ ^ (q - 1) := by sorry
