-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_ihom_free
-- name    : Rep.isZero_tateCohomology_ihom_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/1fbf5abe-9c9c-5d5d-b92f-e66d470694f4
-- title:
--   Tate acyclicity of Hom(ℤ[G]^{(B)},C)
-- statement:
--   Let $G$ be a group which is finite (as a type in `Type`), and let $B$ and $C$ be $\mathbb Z$-linear representations of $G$, i.e. objects of `Rep ℤ G`. Write $\mathbb Z[G]^{(B)}$ for `Rep.free ℤ G B`, the free representation on the underlying set of $B$, and let $((\mathrm{ihom}\,\mathbb Z[G]^{(B)}).\mathrm{obj}\,C)$ be the internal hom of the monoidal closed category `Rep ℤ G`, that is the $\mathbb Z$-module of all $\mathbb Z$-linear maps $\mathbb Z[G]^{(B)} \to C$ equipped with the conjugation action of $G$. The assertion is that for every integer $q$ the object `tateCohomology q` of this representation is a zero object of `ModuleCat ℤ`, hence the zero module. Unfolding the definition of `tateCohomology`, this says: for $q = n+1 \ge 1$ the group cohomology $H^{n+1}(G,-)$ of this representation vanishes; for $q = 0$ the invariants modulo the range of the norm map `normBar` vanish; for $q = -1$ the kernel of `normBar` vanishes; and for $q = -(n+2)$ the group homology $H_{n+1}(G,-)$ vanishes.
--
--   This is the Tate-acyclicity (cohomological triviality) of $\mathrm{Hom}(\mathbb Z[G]^{(B)}, C)$ for a finite group $G$, the internal hom out of a free $\mathbb Z[G]$-module being coinduced from the trivial subgroup. It is used in the $S$-unit computations entering the degree-one Tate duality for the $S$-idèle class formation, where it makes $\mathrm{Ext}^1_G$-classes representable by $G$-equivariant maps out of a free resolution term, and it is cited in that form by [`NumberField.SUnits.exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq`](thm.html#NumberField.SUnits.exists_isGlobalBridge2_apply_eq_continuousH2Spi_of_forall_mul_eq) and [`NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero`](thm.html#NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_ihom_free.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationHomDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.isZero_tateCohomology_ihom_free {G : Type} [Group G] [Fintype G] (B C : Rep ℤ G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom (Rep.free ℤ G B)).obj C).tateCohomology q) := by sorry
