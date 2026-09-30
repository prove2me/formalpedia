-- Prove2me | Theorems.Thm_Smooth4Algebra_region_homology_budget
-- name    : Smooth4Algebra.region_homology_budget
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:38:46.784258+00:00
-- url     : https://prove2.me/theorems/e3d78c98-ef71-4b2a-a04a-7fd93fe9246f
-- title:
--   Homology bound for distinct split regions
-- statement:
--   Let $d:V\to V$ satisfy $d^2=0$ in finite dimension over a field. For a finite family of vector spaces $W_i$, suppose inclusions $\iota_i:W_i\to V$ and projections $p_i:V\to W_i$ satisfy $p_i\iota_i=\mathrm{id}$ and $p_i\iota_j=0$ for $i\ne j$. No spanning assumption is needed. If $o_i$ bounds $\operatorname{rank}(d\iota_i)$ and $u_i$ bounds $\operatorname{rank}(p_i d)$, then
--
--   $$\dim H(V,d)\ge\sum_i\max(0,\dim W_i-o_i-u_i).$$
--
--   Regions may have internal differential entries and need not be subcomplexes. The joint estimate allows their boundary projections and homology images to be dependent.
-- source:
--   Newly authored from cycle21_corner_budget_independent.md, §1 joint cycle-subspace argument; SHA-256 89aa667aee6440fe989e7664eec02f5a7a60010d1d86a77dd094bdf95ba8bdba. This is a new Lean formalization, not an existing source-project theorem split.

import Definitions.Def_Smooth4AlgebraHomology
set_option autoImplicit false
open scoped BigOperators

theorem Smooth4Algebra.region_homology_budget
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (W : ι → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)]
    (d : V →ₗ[K] V) (h_square : d.comp d = 0)
    (inc : ∀ i, W i →ₗ[K] V) (proj : ∀ i, V →ₗ[K] W i)
    (h_retract : ∀ i, (proj i).comp (inc i) = LinearMap.id)
    (h_distinct : ∀ i j, i ≠ j → (proj i).comp (inc j) = 0)
    (outgoing incoming : ι → ℕ)
    (h_outgoing : ∀ i, Module.finrank K (LinearMap.range (d.comp (inc i))) ≤ outgoing i)
    (h_incoming : ∀ i, Module.finrank K (LinearMap.range ((proj i).comp d)) ≤ incoming i) :
    (∑ i, (Module.finrank K (W i) - outgoing i - incoming i)) ≤
      Module.finrank K (Smooth4Algebra.Homology d) := by sorry
