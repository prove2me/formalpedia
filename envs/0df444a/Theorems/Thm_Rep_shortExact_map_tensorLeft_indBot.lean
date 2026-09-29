-- Prove2me | Theorems.Thm_Rep_shortExact_map_tensorLeft_indBot
-- name    : Rep.shortExact_map_tensorLeft_indBot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/35567054-4674-5701-8bac-0f22da582a11
-- title:
--   Induction from the trivial subgroup preserves tensor-exactness
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, both in a fixed universe, let $X$ be a short complex $X_1 \to X_2 \to X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, and let $A$ be such a representation. Write $A.\mathrm{indBot}$ for the representation obtained by inducing along the inclusion of the trivial subgroup $\bot \le G$ the restriction of $A$ to $\bot$; concretely, [`Rep.indBot`](def/GroupCohomology_TateDimensionShift.html#L18) is `Rep.ind` applied to `(⊥ : Subgroup G).subtype` and to `Rep.res` of $A$ along the same map, so its underlying module is the coinvariants of $k[G] \otimes_k A$ for the tensor product of the left regular representation of $\bot$ with the restricted action. The hypothesis is that the image of $X$ under the functor $- \mapsto A \otimes -$, that is the short complex $A \otimes X_1 \to A \otimes X_2 \to A \otimes X_3$ of representations, is short exact (mono at the left, epi at the right, exact in the middle). The conclusion is that the image of $X$ under $- \mapsto A.\mathrm{indBot} \otimes -$ is likewise short exact.
--
--   This is the transfer of short exactness of a tensored short complex from a representation $A$ to the representation induced from the trivial subgroup, the coinduced/induced module used in Tate dimension shifting for group cohomology. It is invoked by [`Rep.shortExact_map_tensorLeft_dimShiftDownObj`](thm.html#Rep.shortExact_map_tensorLeft_dimShiftDownObj) and, through that, by the construction of Tate cup products in [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_map_tensorLeft_indBot.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.shortExact_map_tensorLeft_indBot {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (A : Rep.{u} k G) (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    (X.map (MonoidalCategory.tensorLeft A.indBot)).ShortExact := by sorry
