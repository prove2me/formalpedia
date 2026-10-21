-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_relativisticVortex_limits
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.relativisticVortex_limits
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:31:58.396607+00:00
-- url     : https://prove2.me/theorems/849c53c6-b895-4787-a67c-3bbc5ac8d215
-- title:
--   Core and far-field limits of speed and pressure
-- statement:
--   For $c,W,\rho>0$ define $u(r)=W/[r\sqrt{1+W^2/(c^2r^2)}]$ and $p(r)=\rho c^2[e^{-W^2/(2c^2r^2)}-1]$ for $r>0$. Then
--
--   $$\lim_{r\downarrow0}p(r)=-\rho c^2,\qquad\lim_{r\downarrow0}u(r)=c,\qquad\lim_{r\to\infty}r^2p(r)=-\frac{\rho W^2}{2},\qquad\lim_{r\to\infty}ru(r)=W.$$
--
--   The nonzero constants make the last two limits equivalent to $p\sim-\rho W^2/(2r^2)$ and $u\sim W/r$. No value at the excluded singular core is assigned by these limits.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 8, §IV B, (72)–(74): core and far-field limits

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.8, (72)–(74): limits are taken strictly outside the singular core. -/
theorem relativisticVortex_limits (c W rho : ℝ)
    (hc : 0 < c) (hW : 0 < W) (hrho : 0 < rho) :
    Tendsto (vortexPressure c W rho) (nhdsWithin 0 (Ioi 0)) (nhds (-rho * c ^ 2)) ∧
    Tendsto (vortexSpeed c W) (nhdsWithin 0 (Ioi 0)) (nhds c) ∧
    Tendsto (fun r => r ^ 2 * vortexPressure c W rho r) atTop (nhds (-rho * W ^ 2 / 2)) ∧
    Tendsto (fun r => r * vortexSpeed c W r) atTop (nhds W) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
