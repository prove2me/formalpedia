-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_free_tensor
-- name    : Rep.isZero_tateCohomology_free_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e24314a7-8e94-5f0b-aa21-9ddb70bcc29b
-- title:
--   Tate cohomology of a free k[G]-module tensored with any representation vanishes
-- statement:
--   Let $k$ be a commutative ring, $G$ a group whose underlying type is a fintype, $\alpha$ a type, $M$ an object of $\mathrm{Rep}_k(G)$ (all in a single universe), and $q$ an integer. The assertion is that the degree-$q$ Tate cohomology of the tensor product $\mathrm{Rep.free}\ k\ G\ \alpha \otimes M$, formed in the monoidal structure on $\mathrm{Rep}_k(G)$ (so with the diagonal $G$-action on the tensor product over $k$ of the free $k[G]$-module on $\alpha$ with $M$), is a zero object of $\mathrm{ModuleCat}\ k$ in the sense of `CategoryTheory.Limits.IsZero`, i.e. it is simultaneously initial and terminal. Here the Tate cohomology functor [`Rep.tateCohomology`](def/GroupCohomology_TateCohomology.html#L140) is the piecewise assignment: in degrees $q = n+1 \ge 1$ it is group cohomology $H^{n+1}$ of the representation; in degree $0$ it is the $k$-module of $G$-invariants modulo the range of the map `normBar` attached to the representation; in degree $-1$ it is the kernel of `normBar`; and in degrees $q = -(n+2)$ it is group homology $H_{n+1}$. Thus the vanishing is asserted simultaneously in all four regimes.
--
--   This is the acyclicity of induced (equivalently, free) modules in Tate cohomology, in the form '(free $k[G]$-module) $\otimes$ (arbitrary representation) is Tate-acyclic', obtained by untwisting the diagonal action so that the tensor product becomes induced from the trivial subgroup and then invoking [`Rep.isZero_tateCohomology_indBot`](thm.html#Rep.isZero_tateCohomology_indBot) together with transport of Tate cohomology along an isomorphism of representations. It feeds the construction of free resolutions with prescribed Tate cohomology ([`Rep.exists_shortExact_free_of_forall_isZero`](thm.html#Rep.exists_shortExact_free_of_forall_isZero)), the corresponding statement after restriction to a subgroup ([`Rep.isZero_tateCohomology_res_free`](thm.html#Rep.isZero_tateCohomology_res_free)), and the cup-product criterion [`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_free_tensor.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.isZero_tateCohomology_free_tensor {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (α : Type u) (M : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.free k G α ⊗ M).tateCohomology q) := by sorry
