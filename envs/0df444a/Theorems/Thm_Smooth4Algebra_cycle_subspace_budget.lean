-- Prove2me | Theorems.Thm_Smooth4Algebra_cycle_subspace_budget
-- name    : Smooth4Algebra.cycle_subspace_budget
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:38:35.57877+00:00
-- url     : https://prove2.me/theorems/43f2a248-531e-4e9c-9e6e-940d4e20fb2e
-- title:
--   Cycle-subspace homology bound
-- statement:
--   Let $d:V\to V$ be a square-zero linear map between finite-dimensional vector spaces over a field. Let $S\subseteq\ker d$ be a cycle subspace, and let $p:V\to W$ be linear and injective on $S\cap\operatorname{im}d$. Then
--
--   $$\dim H(V,d)\ge\dim S-\operatorname{rank}(p\circ d).$$
--
--   The right-hand side is truncated at zero when negative. This is the joint cycle-space estimate: it controls dependent boundary projections without asserting independence of separate homology images.
-- source:
--   Newly authored from cycle21_corner_budget_independent.md, §1 joint cycle-subspace argument; SHA-256 89aa667aee6440fe989e7664eec02f5a7a60010d1d86a77dd094bdf95ba8bdba. This is a new Lean formalization, not an existing source-project theorem split.

import Definitions.Def_Smooth4AlgebraHomology
set_option autoImplicit false

theorem Smooth4Algebra.cycle_subspace_budget
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (d : V →ₗ[K] V) (h_square : d.comp d = 0)
    (S : Submodule K V) (h_cycles : S ≤ LinearMap.ker d)
    (p : V →ₗ[K] W)
    (h_injective : Function.Injective
      (p.domRestrict (S ⊓ LinearMap.range d))) :
    Module.finrank K S - Module.finrank K (LinearMap.range (p.comp d)) ≤
      Module.finrank K (Smooth4Algebra.Homology d) := by sorry
