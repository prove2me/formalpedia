-- Prove2me | Theorems.Thm_Rep_indBotPi_indBotSigma
-- name    : Rep.indBotPi_indBotSigma
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/ceb9e760-1556-5702-8e91-31e41a4ee4fa
-- title:
--   The augmentation Ind₁^G Res A → A admits a k-linear section
-- statement:
--   Fix a universe $u$, a commutative ring $k$ and a group $G$, both in that universe, and let $A$ be a $k$-linear representation of $G$, i.e. an object of `Rep k G`. Write $A_* =$ [`Rep.indBot A`](def/GroupCohomology_TateDimensionShift.html#L18) for the representation obtained by restricting $A$ along the inclusion of the trivial subgroup $\bot \le G$ and then inducing back along the same inclusion, that is $\mathrm{Ind}_{1}^{G}\,\mathrm{Res}^{G}_{1}A$. The statement involves two further maps: the morphism of representations [`Rep.indBotπ A`](def/GroupCohomology_TateDimensionShift.html#L27) from $A_*$ to $A$, of which `.hom` denotes the underlying $k$-linear map of modules, and the map [`Rep.indBotσ`](def/GroupCohomology_TateDimensionShift.html#L30), which sends an element of $A$ into $A_*$; on $a$ it is the element `A.indBotMk 1 a`, the generator of the induced module indexed by the identity of $G$. The assertion is that for every element $a$ of the underlying module of $A$, the $k$-linear map underlying [`Rep.indBotπ A`](def/GroupCohomology_TateDimensionShift.html#L27) carries `A.indBotσ a` back to $a$; that is, $\pi \circ \sigma = \mathrm{id}_A$ pointwise.
--
--   This is the statement that the augmentation $\mathrm{Ind}_{1}^{G}\,\mathrm{Res}^{G}_{1}A \to A$ is split by a $k$-linear (not $G$-equivariant) section, so that the short exact sequence $0 \to \ker \pi \to \mathrm{Ind}_{1}^{G}\,\mathrm{Res}^{G}_{1}A \to A \to 0$ is $k$-split; it is the basic input for dimension shifting in Tate cohomology. It is used in the development of Tate cup products, for instance in the associativity of the cup product and in the results on cup-evaluation against the character dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_indBotPi_indBotSigma.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.indBotPi_indBotSigma {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (a : A) :
    (Rep.indBotπ A).hom (A.indBotσ a) = a := by sorry
