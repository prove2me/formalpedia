-- Prove2me | Theorems.Thm_Rep_dimShiftDown_shortExact
-- name    : Rep.dimShiftDown_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/50aa3444-946f-5cbb-b0db-77d7b572ddec
-- title:
--   The dimension-shifting-down sequence is short exact
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (no finiteness is assumed), and let $A$ be a $k$-linear representation of $G$. Write $A_* = \operatorname{Ind}_{\{1\}}^{G}\operatorname{Res}^{G}_{\{1\}} A$ for the representation [`Rep.indBot A`](def/GroupCohomology_TateDimensionShift.html#L18) obtained by inducing along the inclusion of the trivial subgroup $\bot \le G$ the restriction of $A$ to $\bot$, and let $\pi =$ [`Rep.indBotπ A`](def/GroupCohomology_TateDimensionShift.html#L27) be the canonical map $A_* \to A$. The short complex [`Rep.dimShiftDown A`](def/GroupCohomology_TateDimensionShift.html#L42) has as its first term the subrepresentation of $A_*$ carried by the $k$-submodule $\ker(\pi)$ (which is $G$-stable since $\pi$ is a morphism of representations), as its second term $A_*$, as its third term $A$, with first map the inclusion of that subrepresentation and second map $\pi$; composing them is zero by construction. The assertion is that this short complex is short exact in the category $\mathrm{Rep}_k(G)$: the inclusion is a monomorphism, $\pi$ is an epimorphism, and the complex is exact at the middle term.
--
--   This is the 'induced', or projective, half of the dimension-shifting mechanism in group cohomology: it embeds $A$ as a quotient of a representation induced from the trivial subgroup, so that cohomology (or Tate cohomology) of $A$ in one degree is related to that of $\ker(\pi)$ in the next. It is used in the construction of the Tate cup product and its formal properties, being cited in the proofs of associativity, commutativity and the evaluation identities for cup products with the character dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_dimShiftDown_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.dimShiftDown_shortExact {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) :
    (A.dimShiftDown).ShortExact := by sorry
