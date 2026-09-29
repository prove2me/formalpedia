-- Prove2me | Theorems.Thm_WeierstrassCurve_natAbs_apOfModel_le
-- name    : WeierstrassCurve.natAbs_apOfModel_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/33a2c3cf-1381-52c7-bf80-b8ca7e3f2416
-- title:
--   Elementary bound |aₚ|≤ p for an integral Weierstrass model
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, i.e. a tuple of coefficients $a_1,a_2,a_3,a_4,a_6\in\mathbb{Z}$, and let $p$ be a prime. Reducing the coefficients along the ring homomorphism $\mathbb{Z}\to\mathbb{Z}/p$ gives the Weierstrass curve `W.reductionMod p` over $\mathbb{Z}/p$, and the integer `W.apOfModel p` is by definition its trace of Frobenius
--   $$\#(\mathbb{Z}/p) + 1 - \#\bigl((W.\mathrm{reductionMod}\ p)\bigr),$$
--   where the second term is the cardinality of the group of points of the associated affine Weierstrass curve over $\mathbb{Z}/p$, that is, the number of pairs $(x,y)\in(\mathbb{Z}/p)^2$ satisfying the Weierstrass equation at which the curve is nonsingular, together with the point at infinity. The assertion is that the natural-number absolute value of this integer is at most $p$. No nonsingularity or good-reduction hypothesis is imposed on $W$: for singular reductions the singular points are simply not counted, and the bound still holds.
--
--   This is a crude substitute for the Hasse bound $|a_p|\le 2\sqrt{p}$, valid for an arbitrary integral Weierstrass model with no hypothesis on its reduction. It is used in [`WeierstrassCurve.isModularModelOfLevel_div_of_isGoodPrimeFor_of_dvd_of_not_sq_dvd`](thm.html#WeierstrassCurve.isModularModelOfLevel_div_of_isGoodPrimeFor_of_dvd_of_not_sq_dvd), where the point is precisely to exclude the values $\pm(p+1)$ of the trace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_natAbs_apOfModel_le.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.natAbs_apOfModel_le
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    (W.apOfModel p).natAbs ≤ p := by sorry
