-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_relativisticVortex_euler
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.relativisticVortex_euler
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:30:49.137234+00:00
-- url     : https://prove2.me/theorems/321c4bbf-4879-4f60-b2fb-a838c778b9fe
-- title:
--   The constructed relativistic vortex satisfies Euler conservation
-- statement:
--   Let $c,W,\rho>0$, where $\rho$ is constant mass density. Off the vortex axis, use the four-flow $U=(\sqrt{1+W^2/(c^2r^2)},(W/(cr))\mathbf e_\phi)$ and construct
--
--   $$p(r)=\rho c^2\left[e^{-W^2/(2c^2r^2)}-1\right],\qquad T^{\mu\nu}=(\rho c^2+p)U^\mu U^\nu-p\eta^{\mu\nu}.$$
--
--   For every point with $r>0$ and each component $\nu$,
--
--   $$\partial_\mu T^{\mu\nu}=0,\qquad p'(r)=(\rho c^2+p)\frac{W^2}{c^2r^3}.$$
--
--   This is the relativistic Euler conservation law for the specified pressure and circular flow, with conservation as a conclusion rather than an assumed invariant.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 8, §IV B, (69)–(71): relativistic vortex solves Euler equation

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.8, (69)–(71): the constructed negative pressure and relativistic flow
solve the perfect-fluid Euler conservation law. Density is constant. -/
theorem relativisticVortex_euler (c W rho : ℝ) (x : V4)
    (hc : 0 < c) (hW : 0 < W) (hrho : 0 < rho) (hx : 0 < axisRadius x) :
    (∀ j : Fin 4, (∑ i, cartesianPartial (fun y => vortexStress c W rho y i j) x i) = 0) ∧
    (∀ r : ℝ, 0 < r →
      deriv (vortexPressure c W rho) r =
        (rho * c ^ 2 + vortexPressure c W rho r) * W ^ 2 / (c ^ 2 * r ^ 3)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
