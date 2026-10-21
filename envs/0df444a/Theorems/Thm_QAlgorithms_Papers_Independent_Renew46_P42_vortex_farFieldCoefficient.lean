-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_vortex_farFieldCoefficient
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.vortex_farFieldCoefficient
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:33:34.65398+00:00
-- url     : https://prove2.me/theorems/7ef64c77-b8ae-4ee1-8fa3-162accdeae71
-- title:
--   Quadratic inverse-radius coefficient of the radial symbol
-- statement:
--   Let $c,W>0$, $n\ge1$, and fixed real $l$. Set $u(r)=W/[r\sqrt{1+W^2/(c^2r^2)}]$, let $F$ be (77), and write $l_{\mathrm{AB}}=l+(n^2-1)W/c$. Then
--
--   $$\lim_{r\to\infty}r^2[F(r,l)-n^2]=-l_{\mathrm{AB}}^2+(n^2-1)n^2W^2/c^2.$$
--
--   Thus the retained quadratic inverse-radius model is $F_2(r)=n^2-l_{\mathrm{AB}}^2/r^2+(n^2-1)n^2W^2/(c^2r^2)$. This is a fixed-parameter coefficient limit, not a finite-radius identity or a uniform scattering error estimate.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 9, §IV C, (78)–(79): radial far-field coefficient

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.9, (78)–(79): the inverse-radius quadratic coefficient of the full
relativistic-vortex radial symbol; the extra n^2 multiplying W^2 is retained. -/
theorem vortex_farFieldCoefficient (c n W l : ℝ)
    (hc : 0 < c) (hn : 1 ≤ n) (hW : 0 < W) :
    Tendsto (fun r => r ^ 2 * (radialF c n (vortexSpeed c W) r l - n ^ 2)) atTop
      (nhds (-(angularAB c n W l) ^ 2 + (n ^ 2 - 1) * n ^ 2 * W ^ 2 / c ^ 2)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
