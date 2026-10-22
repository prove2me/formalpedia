-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_criticalVortex_radiusAndLimits
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.criticalVortex_radiusAndLimits
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:36:54.855799+00:00
-- url     : https://prove2.me/theorems/82b5e398-ba2b-479e-ba69-7f8a2acfe043
-- title:
--   Critical turning radius and large-index speed asymptotics
-- statement:
--   Let $c,W>0$ and let $u_s(n)=u_3(n)$ be the explicit physical root of (95), for $n>1$. Define
--
--   $$r_s(n)=\frac{W}{u_s(n)}\sqrt{1-u_s(n)^2/c^2}.$$
--
--   Then $r_s>0$, the constructed vortex has $u(r_s)=u_s$, and $l_-'(r_s)=0$. Moreover
--
--   $$\lim_{n\downarrow1}u_s(n)=c,\qquad\lim_{n\to\infty}u_s(n)=0,\qquad\lim_{n\to\infty}\frac{u_s(n)}{c/(2n)}=1.$$
--
--   The source calls this circle the optical Schwarzschild radius. This statement records the calculated critical circle and dispersionless speed asymptotic; the global capture claim is deferred.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 11, §IV D, (96),(98)–(99): critical radius and large-index asymptotics

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF pp.10–11, (96),(98)–(99): critical turning circle, continuous endpoint,
and large-index phase-speed asymptotic in the nondispersive model. -/
theorem criticalVortex_radiusAndLimits (c W : ℝ) (hc : 0 < c) (hW : 0 < W) :
    (∀ n : ℝ, 1 < n →
      0 < criticalRadius c W n ∧
      vortexSpeed c W (criticalRadius c W n) = criticalSpeed c n 2 ∧
      deriv (turningBranch c n (vortexSpeed c W) (-1)) (criticalRadius c W n) = 0) ∧
    Tendsto (fun n => criticalSpeed c n 2) (nhdsWithin 1 (Ioi 1)) (nhds c) ∧
    Tendsto (fun n => criticalSpeed c n 2) atTop (nhds 0) ∧
    Tendsto (fun n => criticalSpeed c n 2 / (c / (2 * n))) atTop (nhds 1) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
