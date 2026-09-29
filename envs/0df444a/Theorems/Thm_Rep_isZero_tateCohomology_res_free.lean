-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_res_free
-- name    : Rep.isZero_tateCohomology_res_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e6f4eb24-7b36-5ced-b41a-b5e7ca468a35
-- title:
--   Restriction of a free representation is Tate-acyclic
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group and $S \le G$ a subgroup which is itself finite; let $\alpha$ be a type and $q$ an integer. Consider the representation $\mathrm{Rep.free}\ k\ G\ \alpha$, the free $k[G]$-module on $\alpha$, and restrict it along the inclusion `S.subtype` to a representation of $S$. The assertion is that the object $\hat H^{q}$ of this restricted representation, namely [`Rep.tateCohomology`](def/GroupCohomology_TateCohomology.html#L140) evaluated at $q$, is a zero object of the category of $k$-modules in the sense of `CategoryTheory.Limits.IsZero`. Here the Tate cohomology of a representation $A$ of a finite group in degree $q$ is defined by cases: for $q = n+1 \ge 1$ it is the group cohomology $H^{n+1}$ of $A$; for $q = 0$ it is the quotient of the invariants of $A$ by the range of the norm map $\rho$.`normBar`; for $q = -1$ it is the kernel of that same norm map; and for $q = -(n+2) \le -2$ it is the group homology $H_{n+1}$ of $A$. Thus all Tate cohomology groups of $S$ acting on a free $k[G]$-module vanish.
--
--   This is the standard acyclicity of induced (here: free, hence relatively injective and relatively projective) modules for Tate cohomology, in the form needed for a subgroup of a finite group. It is used in the treatment of relation modules, feeding [`Rep.exists_hom_relationModuleInt_forall_map_delta_eq`](thm.html#Rep.exists_hom_relationModuleInt_forall_map_delta_eq) and [`Rep.forall_map_delta_eq_zero_iff_exists_eq_sum_rho`](thm.html#Rep.forall_map_delta_eq_zero_iff_exists_eq_sum_rho).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_res_free.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Definitions.Def_GroupCohomology_RelationModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Rep MonoidalCategory

theorem Rep.isZero_tateCohomology_res_free {k G : Type} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (α : Type) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.res S.subtype (Rep.free k G α)).tateCohomology q) := by sorry
