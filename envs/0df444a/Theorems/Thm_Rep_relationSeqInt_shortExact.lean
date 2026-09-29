-- Prove2me | Theorems.Thm_Rep_relationSeqInt_shortExact
-- name    : Rep.relationSeqInt_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/6148d540-798a-5e8a-b487-b44ed4f09910
-- title:
--   Exactness of the canonical free presentation over ℤ
-- statement:
--   Let $G$ be a group and let $B$ be a $\mathbb Z$-linear representation of $G$, i.e. an object of `Rep ℤ G`. The short complex [`Rep.relationSeqInt B`](def/GroupCohomology_RelationModule.html#L84) is built from the following data: its middle term is the free representation `Rep.free ℤ G B` on the underlying set of $B$; its right-hand map is [`Rep.freeCover B`](def/GroupCohomology_RelationModule.html#L15), namely `Rep.freeLift ℤ G B` applied to the identity assignment $b \mapsto b$, so the unique $G$-equivariant map out of the free representation carrying the basis element indexed by $b \in B$ to $b$ itself; its left-hand term is [`Rep.relationModuleInt B`](def/GroupCohomology_RelationModule.html#L73), the object of `Rep ℤ G` obtained by `Rep.of` from the relation representation `relationRepInt B`; and its left-hand map is [`Rep.relationModuleInt.ι B`](def/GroupCohomology_RelationModule.html#L75), the canonical map of that object into the free representation, whose composite with [`Rep.freeCover B`](def/GroupCohomology_RelationModule.html#L15) vanishes, this vanishing being what makes the data a short complex. The theorem asserts that this short complex is short exact in `Rep ℤ G`: the left-hand map is a monomorphism, the right-hand map is an epimorphism, and the complex is exact at the middle term. Equivalently, on underlying $\mathbb Z$-modules the inclusion is injective, the covering map is surjective, and its kernel is exactly the image of the inclusion.
--
--   This is the exactness of the canonical free presentation $0 \to R(B) \to \mathbb Z[G]^{(B)} \to B \to 0$ of a $\mathbb Z[G]$-module by the free module on its own underlying set, in the integral normalisation used throughout the cohomological part of the development. It is the input to dimension-shifting and projectivity arguments, and is cited in the construction of maps out of $H^1$ and in the Herbrand-quotient computations for idele class groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_relationSeqInt_shortExact.lean

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

theorem Rep.relationSeqInt_shortExact {G : Type} [Group G] (B : Rep ℤ G) :
    (Rep.relationSeqInt B).ShortExact := by sorry
