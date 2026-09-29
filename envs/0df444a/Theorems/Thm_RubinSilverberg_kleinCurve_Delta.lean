-- Prove2me | Theorems.Thm_RubinSilverberg_kleinCurve_Delta
-- name    : RubinSilverberg.kleinCurve_Delta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/f4c0a4b0-af81-55f5-abcd-3fb385a6b27f
-- title:
--   Discriminant of Klein's level-5 curve: Δ = -V(u)⁵
-- statement:
--   Let $K$ be a field of characteristic zero and let $u \in K$. Consider the Weierstrass curve `kleinCurve u` over $K$ given by the coefficient tuple $(a_1,a_2,a_3,a_4,a_6) = (0,0,0,-H(u)/48,\;T(u)/864)$, i.e. the curve $y^2 = x^3 - \frac{H(u)}{48}x + \frac{T(u)}{864}$, where
--   $$H(u) = u^{20} - 228u^{15} + 494u^{10} + 228u^{5} + 1, \qquad T(u) = u^{30} + 522u^{25} - 10005u^{20} - 10005u^{10} - 522u^{5} + 1.$$
--   The assertion is that its discriminant, in the Mathlib normalisation $\Delta = -b_2^2 b_8 - 8b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6$ computed from these coefficients, equals
--   $$\Delta(\mathtt{kleinCurve}\ u) = -\,V(u)^5, \qquad V(u) = u\,(u^{10} + 11u^{5} - 1).$$
--   The characteristic-zero hypothesis is what makes the divisions by $48$ and $864$ meaningful and lets the resulting identity of rational expressions be cleared of denominators.
--
--   The curve is Klein's level-$5$ model, the universal elliptic curve with full level-$5$ structure over $X(5) \cong \mathbb{P}^1_u$, written in terms of the icosahedral forms $V$, $H$, $T$; the displayed discriminant is equivalent to the syzygy $T^2 - H^3 = 1728\,V^5$ and shows that the curve is nonsingular exactly away from the twelve zeros of $V$. It is used in the Rubin–Silverberg construction of families of elliptic curves with constant mod-$5$ representation, and is cited here by the results producing the prescribed $5$-torsion point and the associated isomorphism of torsion modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_kleinCurve_Delta.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.kleinCurve_Delta {K : Type*} [Field K] [CharZero K] (u : K) : (kleinCurve u).Δ = -kleinV u ^ 5 := by sorry
