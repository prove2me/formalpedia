-- Prove2me | Theorems.Thm_Rep_bijective_tateDelta_dimShiftUp
-- name    : Rep.bijective_tateDelta_dimShiftUp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/b9ba21c8-4e15-5b64-a8a9-94caaa4ad9eb
-- title:
--   Dimension shifting: δ is bijective for 0→ A→ Ind Res A→ A'→ 0
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $A$ be a $k$-linear representation of $G$. Write $A_*$ for `A.indBot`, the representation induced along the inclusion of the trivial subgroup $\bot \le G$ from the restriction of $A$ to $\bot$, and let $\iota =$ `indBotι A` be the canonical map $A \to A_*$; the short complex `A.dimShiftUp` has $X_1 = A$, $X_2 = A_*$ and $X_3 =$ `A.dimShiftUpObj`, the quotient of $A_*$ by the range of $\iota$ with its induced $G$-action, with maps $\iota$ and the quotient projection. Assume `hA`, that this short complex is short exact in the category of $k$-linear $G$-representations, and let $n \in \mathbb{Z}$. The conclusion is that the underlying $k$-linear map of the connecting morphism [`Rep.tateδ hA n`](def/GroupCohomology_TateShiftMaps.html#L32), from the degree-$n$ Tate cohomology of the quotient $X_3$ to the degree-$(n+1)$ Tate cohomology of $A$, is bijective as a function.
--
--   This is the map-level form of dimension shifting up for Tate cohomology of a finite group: the connecting map of the sequence $0 \to A \to \mathrm{Ind}^G_1\mathrm{Res}^G_1 A \to A' \to 0$ is an isomorphism in every degree. It underlies the degree-shifting isomorphisms used to define and to verify the properties (associativity, commutativity, compatibility with maps of representations) of Tate cup products in negative degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_bijective_tateDelta_dimShiftUp.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.bijective_tateDelta_dimShiftUp {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (hA : A.dimShiftUp.ShortExact) (n : ℤ) :
    Function.Bijective (Rep.tateδ hA n).hom := by sorry
