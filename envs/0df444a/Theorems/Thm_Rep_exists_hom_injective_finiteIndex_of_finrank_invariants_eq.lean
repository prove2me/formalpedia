-- Prove2me | Theorems.Thm_Rep_exists_hom_injective_finiteIndex_of_finrank_invariants_eq
-- name    : Rep.exists_hom_injective_finiteIndex_of_finrank_invariants_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/8a66163e-bf15-5c3c-b802-51af64e9873c
-- title:
--   Commensurability of ℤ[G]-lattices with equal invariant ranks, G cyclic
-- statement:
--   Let $G$ be a finite cyclic group and let $L$, $L'$ be objects of `Rep ℤ G`, i.e. $\mathbb{Z}$-modules with a $G$-action by $\mathbb{Z}$-linear automorphisms, each assumed finitely generated and free over $\mathbb{Z}$. Assume that for every subgroup $H \leq G$ the $\mathbb{Z}$-rank of the degree-$0$ group cohomology of the restriction of $L$ along the inclusion $H \hookrightarrow G$ — that is, of the module of $H$-invariants $L^{H}$ — equals the $\mathbb{Z}$-rank of the corresponding degree-$0$ group cohomology of the restriction of $L'$, so $\operatorname{rk}_{\mathbb{Z}} L^{H} = \operatorname{rk}_{\mathbb{Z}} (L')^{H}$ for all $H$. The conclusion is that there exists a morphism $f : L \to L'$ in `Rep ℤ G`, i.e. a $G$-equivariant $\mathbb{Z}$-linear map, such that the underlying map of $f$ is injective and the image of $f$, viewed as an additive subgroup of $L'$, has finite index. Thus the two lattices are commensurable through an equivariant embedding.
--
--   The statement is the integral form of the fact that a rational representation of a cyclic group is determined up to isomorphism by the dimensions of the invariants of its restrictions to all subgroups: two $\mathbb{Z}[G]$-lattices with matching invariant ranks at every subgroup admit an equivariant embedding of finite index. It is used in the construction of an equivariant isomorphism after tensoring with $\mathbb{Z}/p$-type coefficients, via [`Rep.nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq`](thm.html#Rep.nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_hom_injective_finiteIndex_of_finrank_invariants_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.exists_hom_injective_finiteIndex_of_finrank_invariants_eq
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    (L L' : Rep ℤ G) [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L']
    (h : ∀ H : Subgroup G, Module.finrank ℤ (groupCohomology (Rep.res H.subtype L) 0) =
      Module.finrank ℤ (groupCohomology (Rep.res H.subtype L') 0)) :
    ∃ f : L ⟶ L', Function.Injective f.hom ∧ (f.hom : L →+ L').range.FiniteIndex := by sorry
