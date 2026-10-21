-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_relativisticVortex_profile
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.relativisticVortex_profile
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:30:02.076996+00:00
-- url     : https://prove2.me/theorems/988ed78f-7ffc-4f8c-9403-004bee8b324c
-- title:
--   Subluminal relativistic circular flow and continuity
-- statement:
--   Let $c,W,r>0$. Define $\gamma(r)=\sqrt{1+W^2/(c^2r^2)}$ and $u(r)=W/(r\gamma(r))$. In Cartesian spacetime coordinates, let $r=\sqrt{x^2+y^2}>0$, $\mathbf e_\phi=(-y/r,x/r,0)$ and $\mathbf u=u(r)\mathbf e_\phi$. Then
--
--   $$0<u(r)<c,\quad (1-u(r)^2/c^2)^{-1/2}=\gamma(r),\quad U=\gamma(1,\mathbf u/c)=\left(\gamma,-\frac{Wy}{cr^2},\frac{Wx}{cr^2},0\right),\quad U^T\eta U=1,\quad\partial_\mu U^\mu=0.$$
--
--   More generally, every stationary differentiable axisymmetric circular speed profile with $|u(r)|<c$ has divergence-free normalized four-flow away from the axis.
--
--   The Cartesian four-vector retains the azimuthal direction and the spatial factor $1/c$.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 8, §IV B, (65)–(68): subluminal relativistic circular flow

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.8, (65)–(68), and (53): the relativistic circular flow is subluminal,
has the stated Lorentz factor, and obeys continuity off the excluded axis. -/
theorem relativisticVortex_profile (c W r : ℝ) (x : V4)
    (hc : 0 < c) (hW : 0 < W) (hr : 0 < r) (hx : 0 < axisRadius x) :
    0 < vortexSpeed c W r ∧ vortexSpeed c W r < c ∧
    1 / Real.sqrt (1 - (vortexSpeed c W r) ^ 2 / c ^ 2) = vortexGamma c W r ∧
    fourFlow c (vortexFlow c W x) = vortexFour c W x ∧
    quadratic minkowskiMetric (vortexFour c W x) = 1 ∧ divergence4 (vortexFour c W) x = 0 ∧
    (∀ v : ℝ → ℝ, DifferentiableAt ℝ v (axisRadius x) → |v (axisRadius x)| < c →
      divergence4 (fun y => fourFlow c (circularFlow v y)) x = 0) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
