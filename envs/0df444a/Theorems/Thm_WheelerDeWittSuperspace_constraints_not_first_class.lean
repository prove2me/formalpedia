-- Prove2me | Theorems.Thm_WheelerDeWittSuperspace_constraints_not_first_class
-- name    : WheelerDeWittSuperspace.constraints_not_first_class
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T23:14:55.804024+00:00
-- url     : https://prove2.me/theorems/637c762a-5644-4499-9230-892bf96e5223
-- title:
--   Lattice Hamiltonian constraints are second class
-- statement:
--   Let $\kappa\neq0$, let each $R(\cdot,z)$ be $C^1$, let $h$ be a physical configuration and $x\neq y$ two sites. Suppose the potential at $y$ depends on the metric at $x$, in the sense that the symmetric part of $\partial V_y/\partial h_{ab}(x)$ is nonzero at $h$. Then there are momenta $p$ such that **every** lattice constraint vanishes,
--   $$H_z(h,p)=0\quad\text{for all } z,$$
--   and yet
--   $$\{H_x,H_y\}(h,p)\neq0 .$$
--   Hence the lattice constraints are not first class. Every finite-difference scalar curvature couples neighbouring sites, so this applies to every such discretization of the Wheeler–DeWitt constraint.
-- source:
--   R. Loll, Discrete approaches to quantum gravity in four dimensions, Living Rev. Relativ. 1 (1998), Section 2.12, https://arxiv.org/abs/gr-qc/9805049; B. Dittrich, https://arxiv.org/abs/0810.3594, p. 6; B. Bahr, B. Dittrich, https://arxiv.org/abs/0905.1670; M. Bander, Phys. Rev. D 36 (1987) 2297

import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

/-- Goal (lattice constraints are second class): as soon
as the potential at `y` depends on the metric at a different site `x` (as for any
finite-difference curvature), there is a point on the constraint surface where the two
constraints do not Poisson-commute. -/
theorem constraints_not_first_class {X : Type*} [Fintype X] [DecidableEq X] (kappa Lam : ℝ)
    (hkappa : kappa ≠ 0) (R : Config X → X → ℝ) (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z))
    (h : Config X) (hh : IsPhysical h) (x y : X) (hxy : x ≠ y)
    (hdep : ∃ a b, partialR (fun h' => potentialAt kappa Lam R h' y) x a b h +
        partialR (fun h' => potentialAt kappa Lam R h' y) x b a h ≠ 0) :
    ∃ p : Config X, (∀ z, classicalConstraint kappa Lam R z (h, p) = 0) ∧
      poisson (classicalConstraint kappa Lam R x) (classicalConstraint kappa Lam R y) (h, p) ≠ 0 := by sorry

end WheelerDeWittSuperspace
