-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_idealVortex_scaling
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.idealVortex_scaling
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:37:26.954172+00:00
-- url     : https://prove2.me/theorems/cac4968b-4d16-4f1d-9a74-f097598cbaa2
-- title:
--   Ideal-vortex coordinate and phase scaling
-- statement:
--   Let $c,W>0$, $n\ge1$, and a real phase $S(t,r,\phi)$ be differentiable at the point considered. For $\bar r>0$, construct its coordinate pullback
--
--   $$\bar S(\bar t,\bar r,\phi)=\frac cW S\!\left(\frac W{c^2}\bar t,\frac Wc\bar r,\phi\right).$$
--
--   The vortex speed obeys $u_{c,W}(W\bar r/c)/c=u_{1,1}(\bar r)$. If $\mathcal E_{c,n,u}[S]$ denotes the cylindrical Hamilton–Jacobi symbol in (75), then
--
--   $$\mathcal E_{1,n,u_{1,1}}[\bar S](\bar t,\bar r,\phi)=c^{-2}\mathcal E_{c,n,u_{c,W}}[S](W\bar t/c^2,W\bar r/c,\phi).$$
--
--   Hence the dimensionless ideal-vortex equation is independent of $W$. For $a,\omega,r>0$, the loop phase is unchanged by $(W,r,\omega)\mapsto(aW,ar,\omega/a)$; for $n_0>1$ the critical radius satisfies $r_s(c,aW,n_0)=a\,r_s(c,W,n_0)$.
--
--   This is a coordinate and phase scaling, without a fixed-observation-distance zero-vorticity limit or a finite-core capture conclusion.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 11, §IV E, (100): scale invariance of ideal vortex rays and phase scaling

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF pp.11–12, (100): coordinate pullback removes W from the ideal-vortex
Hamilton–Jacobi equation; phase is preserved by inverse frequency scaling.
This is not a fixed-distance W-to-zero or finite-core capture assertion. -/
theorem idealVortex_scaling (c n W : ℝ) (S : V3 → ℝ) (z : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hW : 0 < W) (hz : 0 < z 1)
    (hS : DifferentiableAt ℝ S ![W / c ^ 2 * z 0, W / c * z 1, z 2]) :
    vortexSpeed c W (W / c * z 1) / c = vortexSpeed 1 1 (z 1) ∧
    cylindricalSymbol 1 n (vortexSpeed 1 1) (scaledEikonal c W S) z =
      cylindricalSymbol c n (vortexSpeed c W) S
        ![W / c ^ 2 * z 0, W / c * z 1, z 2] / c ^ 2 ∧
    (∀ (omega a r : ℝ), 0 < omega → 0 < a → 0 < r →
      vortexPhase c n (omega / a) (a * W) (a * r) = vortexPhase c n omega W r) ∧
    (∀ (a n0 : ℝ), 0 < a → 1 < n0 →
      criticalRadius c (a * W) n0 = a * criticalRadius c W n0) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
