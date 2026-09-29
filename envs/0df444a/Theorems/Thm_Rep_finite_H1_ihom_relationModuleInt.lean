-- Prove2me | Theorems.Thm_Rep_finite_H1_ihom_relationModuleInt
-- name    : Rep.finite_H1_ihom_relationModuleInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/a931fdd4-94e1-5890-886d-8c65e8f6c5bd
-- title:
--   Finiteness of H¹ of the internal hom from a relation module
-- statement:
--   Let $G$ be a group whose underlying type is finite, let $B$ be an object of $\mathrm{Rep}_{\mathbb Z}(G)$ whose underlying set is equipped with a `Fintype` structure, and let $E$ be an object of $\mathrm{Rep}_{\mathbb Z}(G)$ whose underlying $\mathbb Z$-module is finitely generated. Write [`Rep.relationModuleInt B`](def/GroupCohomology_RelationModule.html#L73) for the integral representation $\mathrm{Rep.of}$ applied to [`Rep.relationRepInt B`](def/GroupCohomology_RelationModule.html#L55), that is, the $G$-representation on the abelian group [`Rep.relationCarrier B`](def/GroupCohomology_RelationModule.html#L50) whose action of $g \in G$ is the $\mathbb Z$-linear map induced by the additive automorphism given by the action of $g$ in [`Rep.relationModule B`](def/GroupCohomology_RelationModule.html#L18). Form the internal hom object $(\mathrm{ihom}\,(\mathrm{Rep.relationModuleInt}\ B))(E)$ of the closed monoidal category $\mathrm{Rep}_{\mathbb Z}(G)$, i.e. the group $\mathrm{Hom}_{\mathbb Z}(\mathrm{Rep.relationCarrier}\ B, E)$ with the conjugation action of $G$. The assertion is that the first group-cohomology group `groupCohomology.H1` of this representation is finite.
--
--   This is the finiteness of $H^1\bigl(G,\mathrm{Hom}_{\mathbb Z}(R(B),E)\bigr)$ for a finite group $G$, a finite module $B$ and a module $E$ finitely generated over $\mathbb Z$ — an instance of the finiteness of the cohomology of a finite group with finitely generated coefficients. It supplies the finiteness needed in the construction of the degree-two global Tate-duality bridge for $S$-units, where it is used by [`NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero`](thm.html#NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_finite_H1_ihom_relationModuleInt.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.finite_H1_ihom_relationModuleInt {G : Type} [Group G] [Finite G] (B : Rep ℤ G) [Fintype B] (E : Rep ℤ G)
    [Module.Finite ℤ E] : Finite (groupCohomology.H1 ((ihom (Rep.relationModuleInt B)).obj E)) := by sorry
