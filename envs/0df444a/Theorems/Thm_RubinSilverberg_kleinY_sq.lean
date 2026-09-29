-- Prove2me | Theorems.Thm_RubinSilverberg_kleinY_sq
-- name    : RubinSilverberg.kleinY_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/d1e2e7a9-77e3-5757-9879-9f8b6146182f
-- title:
--   Rubin–Silverberg section lies on Klein's level-5 curve
-- statement:
--   Let $K$ be a field of characteristic zero and $u \in K$. Write
--   $$\mathrm{kleinX}(u) = \tfrac{1}{12}\bigl(u^{10} + 12u^{8} - 12u^{7} + 24u^{6} + 30u^{5} + 60u^{4} + 36u^{3} + 24u^{2} + 12u + 1\bigr),$$
--   $$\mathrm{kleinY}(u) = \tfrac{1}{2}\bigl(u^{13} + u^{12} + 4u^{11} + 5u^{9} + 6u^{8} + 21u^{7} + 29u^{6} + 25u^{5} + 15u^{4} + 9u^{3} + 4u^{2} + u\bigr),$$
--   and let
--   $$\mathrm{kleinH}(u) = u^{20} - 228u^{15} + 494u^{10} + 228u^{5} + 1,$$
--   $$\mathrm{kleinT}(u) = u^{30} + 522u^{25} - 10005u^{20} - 10005u^{10} - 522u^{5} + 1$$
--   be the two polynomial invariants (defined over any commutative ring). The assertion is the identity
--   $$\mathrm{kleinY}(u)^{2} = \mathrm{kleinX}(u)^{3} + \frac{-\mathrm{kleinH}(u)}{48}\,\mathrm{kleinX}(u) + \frac{\mathrm{kleinT}(u)}{864}$$
--   in $K$, for every such $u$; that is, the point with coordinates $(\mathrm{kleinX}(u), \mathrm{kleinY}(u))$ satisfies the short Weierstrass equation $y^{2} = x^{3} - \frac{\mathrm{kleinH}(u)}{48}x + \frac{\mathrm{kleinT}(u)}{864}$. The characteristic-zero hypothesis makes the denominators $2$, $12$, $48$ and $864$ invertible; no further condition on $u$ is imposed.
--
--   This is the verification that Rubin and Silverberg's explicit section of the Klein family of elliptic curves with fixed level-$5$ structure really lands on the curve $y^2 = x^3 - \frac{H(u)}{48}x + \frac{T(u)}{864}$. It is used by [`RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul`](thm.html#RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul), where the resulting point is shown to be a nonzero point of order dividing $5$, which is the starting point for the constancy of the mod-$5$ representation along the family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_kleinY_sq.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.kleinY_sq {K : Type*} [Field K] [CharZero K] (u : K) : kleinY u ^ 2 = kleinX u ^ 3 + (-kleinH u / 48) * kleinX u + kleinT u / 864 := by sorry
