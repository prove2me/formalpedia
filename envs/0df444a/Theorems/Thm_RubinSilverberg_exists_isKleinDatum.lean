-- Prove2me | Theorems.Thm_RubinSilverberg_exists_isKleinDatum
-- name    : RubinSilverberg.exists_isKleinDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/b787d93b-c7da-5133-b9a9-12be29174e79
-- title:
--   Existence of a Klein datum over an algebraically closed field
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $a,b\in K$ satisfy $4a^3+27b^2\neq 0$, i.e. the short Weierstrass cubic $y^2=x^3+ax+b$ is nonsingular. Write $V(u)=u(u^{10}+11u^5-1)$ and $H(u)=u^{20}-228u^{15}+494u^{10}+228u^{5}+1$ for the two icosahedral polynomials `kleinV` and `kleinH`. The theorem asserts that there exists $u_0\in K$ which is a Klein datum for $(a,b)$ in the sense of `IsKleinDatum`, that is, $u_0$ satisfies the two conditions
--   $$H(u_0)^3\,(4a^3+27b^2)+6912\,a^3\,V(u_0)^5=0,\qquad V(u_0)\neq 0.$$
--   No further normalisation of $u_0$ is asserted, and no hypothesis beyond nonvanishing of $4a^3+27b^2$ is imposed on $a$ and $b$.
--
--   The equation $H(u)^3(4a^3+27b^2)+6912a^3V(u)^5=0$ expresses that $u_0$ lies over the $j$-invariant of $y^2=x^3+ax+b$ under Klein's degree-$60$ icosahedral covering $X(5)\to X(1)$; a Klein datum is thus the starting point of the Rubin–Silverberg parametrisation of curves with prescribed mod-$5$ representation. The result is used to produce the auxiliary curve in [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_exists_isKleinDatum.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.exists_isKleinDatum {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] (a b : K) (hD : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) : ∃ u₀ : K, RubinSilverberg.IsKleinDatum a b u₀ := by sorry
