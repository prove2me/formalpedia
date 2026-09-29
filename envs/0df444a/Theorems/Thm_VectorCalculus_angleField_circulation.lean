-- Prove2me | Theorems.Thm_VectorCalculus_angleField_circulation
-- name    : VectorCalculus.angleField_circulation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T00:21:34.946237+00:00
-- url     : https://prove2.me/theorems/a76a6f08-07e8-4268-b510-ef20b1d1f6be
-- title:
--   $\oint_{|\mathbf{x}|=R} \mathbf{F}\cdot d\mathbf{x} = 2\pi$ for the angle field
-- statement:
--   For the planar field $\mathbf F = \bigl(-y/(x^2+y^2),\ x/(x^2+y^2)\bigr)$ and the circle of radius $R > 0$ about the origin, parametrised by $\mathbf x(t) = (R\cos t, R\sin t)$ with $t$ running from $0$ to $2\pi$,
--
--   $$\oint_C \mathbf F\cdot d\mathbf x = \int_0^{2\pi}\left(-\frac{\sin t}{R}\cdot(-R\sin t) + \frac{\cos t}{R}\cdot R\cos t\right)dt = 2\pi .$$
--
--   The value is independent of $R$ and, in particular, nonzero.
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.4 (p. 25), the computation $\oint_C \mathbf F\cdot d\mathbf x = 2\pi$ for $\mathbf x(t) = (R\cos t, R\sin t)$

import Definitions.Def_VectorCalculus_lineIntegral
import Definitions.Def_VectorCalculus_angleField

namespace VectorCalculus

theorem angleField_circulation (R : ℝ) (hR : 0 < R) :
    lineIntegral angleField (fun t => ![R * Real.cos t, R * Real.sin t]) 0 (2 * Real.pi)
      = 2 * Real.pi := by sorry

end VectorCalculus
