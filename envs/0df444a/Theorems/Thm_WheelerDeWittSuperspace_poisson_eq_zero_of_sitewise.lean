-- Prove2me | Theorems.Thm_WheelerDeWittSuperspace_poisson_eq_zero_of_sitewise
-- name    : WheelerDeWittSuperspace.poisson_eq_zero_of_sitewise
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-05T23:01:46.412986+00:00
-- url     : https://prove2.me/theorems/e385a6bd-f408-4da8-8b99-4415fa7d0477
-- title:
--   Site-local potentials give Poisson-commuting constraints
-- statement:
--   If for every site $z$ the potential $R(h,z)$ depends only on $h(z)$ (and is $C^1$), then the classical lattice constraints $H_z=2\kappa\,G_{abcd}(h(z))\,p^{ab}(z)p^{cd}(z)+V_z(h)$ satisfy
--   $$\{H_x,H_y\}=0$$
--   at every point $(h,p)$ with $h$ physical. This is the ultralocal (strong-coupling) case.
-- source:
--   C. J. Isham, Proc. R. Soc. Lond. A 351 (1976) 209; K. Pilati, Phys. Rev. D 26 (1982) 2645, https://doi.org/10.1103/PhysRevD.26.2645

import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Milestone 7 (ultralocal case is first class): if every potential depends only on
the metric at its own site (the strong-coupling regime), the classical constraints
Poisson-commute everywhere. -/
theorem poisson_eq_zero_of_sitewise {X : Type*} [Fintype X] [DecidableEq X] (kappa Lam : ℝ)
    (hkappa : kappa ≠ 0)
    (R : Config X → X → ℝ) (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z))
    (hloc : ∀ z (h h' : Config X), h z = h' z → R h z = R h' z)
    (x y : X) (w : Phase X) (hw : IsPhysical w.1) :
    poisson (classicalConstraint kappa Lam R x) (classicalConstraint kappa Lam R y) w = 0 := by sorry

end WheelerDeWittSuperspace
