-- Prove2me | Theorems.Thm_Rep_homSeqOne_shortExact
-- name    : Rep.homSeqOne_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/54926ddf-23cd-549c-81d4-77d09ac5ae21
-- title:
--   Left exactness of Hom(-,E) on the free presentation
-- statement:
--   Let $G$ be a group and let $B$ and $E$ be objects of $\mathrm{Rep}\,\mathbb Z\,G$, that is, $\mathbb Z$-linear representations of $G$; there are no further hypotheses. The assertion is that the three-term complex [`Rep.homSeq₁ B E`](def/GroupCohomology_RelationHomDefect.html#L59) of representations is short exact, i.e. its first map is a monomorphism, its second map is an epimorphism, and the sequence is exact in the middle. The complex has middle term the internal hom $(\mathrm{ihom}\,(\mathrm{Rep.free}\ \mathbb Z\ G\ B)).\mathrm{obj}\ E$, the representation of $\mathbb Z$-linear maps from the free $\mathbb Z[G]$-module on the underlying set of $B$ to $E$; its left-hand term is $(\mathrm{ihom}\,B).\mathrm{obj}\ E$, mapped in by [`Rep.preHom (Rep.freeCover B) E`](def/GroupCohomology_RelationHomDefect.html#L21), precomposition with the canonical surjection [`Rep.freeCover B`](def/GroupCohomology_RelationModule.html#L15) from the free module onto $B$ (which sends the generator at $b$ to $b$), so that the underlying linear map of the image of $x$ is $a \mapsto x((\mathrm{Rep.freeCover}\ B)(a))$; its right-hand term is the image of [`Rep.preHom (Rep.relationModuleInt.ι B) E`](def/GroupCohomology_RelationHomDefect.html#L21), restriction of maps along the inclusion of the relation module [`Rep.relationModuleInt B`](def/GroupCohomology_RelationModule.html#L73) (the kernel of [`Rep.freeCover B`](def/GroupCohomology_RelationModule.html#L15)), and the second map is the corestriction of that restriction map to its image.
--
--   This is the left exactness of $\mathrm{Hom}(-,E)$ applied to the canonical free presentation $R(B)\to \mathbb Z[G]^{(B)}\to B\to 0$ of a $\mathbb Z$-linear representation, packaged as a short exact sequence with third term the image of the restriction-to-relations map. It is used in the $S$-unit cohomology part of the development, where it is cited in the analysis of global bridge maps and of the vanishing of classes after passing to a level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_homSeqOne_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RelationHomDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

theorem Rep.homSeqOne_shortExact {G : Type} [Group G] (B E : Rep ℤ G) : (Rep.homSeq₁ B E).ShortExact := by sorry
