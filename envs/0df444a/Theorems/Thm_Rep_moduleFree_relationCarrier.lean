-- Prove2me | Theorems.Thm_Rep_moduleFree_relationCarrier
-- name    : Rep.moduleFree_relationCarrier
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/d46ac9d8-865b-58d6-90b8-5beb633c0acc
-- title:
--   ℤ-freeness of the relation module carrier
-- statement:
--   Let $G$ be a finite group and let $B$ be an object of $\mathrm{Rep}\,\mathbb{Z}\,G$, that is, a $\mathbb{Z}$-module with an action of $G$, whose underlying type is assumed finite. Form the free representation `Rep.free ℤ G B` on the underlying type of $B$, together with its canonical map `freeCover B` onto $B$; the project's `relationModule B` is the subrepresentation of `Rep.free ℤ G B` carried by the kernel of the underlying $\mathbb{Z}$-linear map of `freeCover B`, this submodule being $G$-stable because the $G$-action commutes with a morphism of representations. The type [`Rep.relationCarrier B`](def/GroupCohomology_RelationModule.html#L50) is by definition the underlying type of `relationModule B`, equipped with its resulting $\mathbb{Z}$-module structure. The assertion is that [`Rep.relationCarrier B`](def/GroupCohomology_RelationModule.html#L50) is a free $\mathbb{Z}$-module, i.e. `Module.Free ℤ (Rep.relationCarrier B)` holds. No claim is made about the rank, nor about the $G$-action: the conclusion concerns only the additive structure of the relation module.
--
--   This is the elementary freeness statement for the relation module $R(B)=\ker(\mathbb{Z}[G]^{(B)}\to B)$ attached to a finite $\mathbb{Z}[G]$-module $B$: as a subgroup of a free abelian group of finite rank it is again free. It is used where relation modules are resolved or mapped into, for instance by [`Rep.exists_hom_relationModuleInt_forall_map_delta_eq`](thm.html#Rep.exists_hom_relationModuleInt_forall_map_delta_eq), [`Rep.exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective`](thm.html#Rep.exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective) and [`Rep.finite_H1_ihom_relationModuleInt`](thm.html#Rep.finite_H1_ihom_relationModuleInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_moduleFree_relationCarrier.lean

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

theorem Rep.moduleFree_relationCarrier {G : Type} [Group G] [Fintype G] (B : Rep ℤ G) [Fintype B] :
    Module.Free ℤ (Rep.relationCarrier B) := by sorry
