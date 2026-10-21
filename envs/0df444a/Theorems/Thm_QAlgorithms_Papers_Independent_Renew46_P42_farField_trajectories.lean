-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_farField_trajectories
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.farField_trajectories
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:34:17.456954+00:00
-- url     : https://prove2.me/theorems/5866c5f4-99f5-4ec5-8dc1-34c357e66ca8
-- title:
--   Signed trajectories in the retained far-field model
-- statement:
--   Let $c,W>0$, $n\ge1$, $L=l+(n^2-1)W/c\ne0$, and $r_0=\sqrt{L^2/n^2-(n^2-1)W^2/c^2}>0$. Set $F_2(r)=n^2-L^2/r^2+(n^2-1)n^2W^2/(c^2r^2)$ and choose real $\phi_0$. For every $r\ge r_0$, the endpoint-singular integrand is interval-integrable and
--
--   $$\phi(r)-\phi_0=\int_{r_0}^r\frac{L\,ds}{s^2\sqrt{F_2(s)}}=\frac{L}{nr_0}\arccos(r_0/r).$$
--
--   Writing $\phi_\infty=\phi_0+\pi L/(2nr_0)$, one has
--
--   $$\lim_{r\to\infty}\phi(r)=\phi_\infty,\qquad\lim_{r\to\infty}r\sin(\phi(r)-\phi_\infty)=-L/n.$$
--
--   On discarding the explicit $W^2$ term, the signed outgoing angle becomes $\operatorname{sgn}(L)\arccos(|L|/(nr))$ and obeys $r\cos(\phi-\phi_0)=|L|/n$ for $r\ge|L|/n$.
--
--   These exact identities belong to the retained radial models and keep both signs of the angular momentum.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 9, §IV C, (80)–(86): trajectories of the retained far-field model

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.9, (81)–(86): signed trajectories of the retained far-field model.
The endpoint singularity is explicitly integrable. No full-flow scattering
error estimate or unsigned physical deflection is asserted. -/
theorem farField_trajectories (c n W l phiBase : ℝ)
    (hc : 0 < c) (hn : 1 ≤ n) (hW : 0 < W)
    (hl : angularAB c n W l ≠ 0)
    (hradicand : 0 < (angularAB c n W l) ^ 2 / n ^ 2 - (n ^ 2 - 1) * W ^ 2 / c ^ 2) :
    (∀ r : ℝ, farTurningRadius c n W l ≤ r →
      IntervalIntegrable (fun s => angularAB c n W l / (s ^ 2 * Real.sqrt (farRadial c n W l s)))
        volume (farTurningRadius c n W l) r ∧
      (∫ s in (farTurningRadius c n W l)..r,
        angularAB c n W l / (s ^ 2 * Real.sqrt (farRadial c n W l s))) =
          farAngle c n W l phiBase r - phiBase) ∧
    Tendsto (farAngle c n W l phiBase) atTop
      (nhds (phiBase + Real.pi * angularAB c n W l / (2 * n * farTurningRadius c n W l))) ∧
    Tendsto (fun r => r * Real.sin (farAngle c n W l phiBase r -
      (phiBase + Real.pi * angularAB c n W l / (2 * n * farTurningRadius c n W l))))
      atTop (nhds (-angularAB c n W l / n)) ∧
    (∀ r : ℝ, |angularAB c n W l| / n ≤ r →
      r * Real.cos ((angularAB c n W l / |angularAB c n W l|) *
        Real.arccos (|angularAB c n W l| / (n * r))) = |angularAB c n W l| / n) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
