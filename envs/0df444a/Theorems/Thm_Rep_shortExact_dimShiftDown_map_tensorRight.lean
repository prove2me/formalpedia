-- Prove2me | Theorems.Thm_Rep_shortExact_dimShiftDown_map_tensorRight
-- name    : Rep.shortExact_dimShiftDown_map_tensorRight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/f3888236-c1fc-559d-9d45-f27a0cf37e73
-- title:
--   Dimension-shifting sequence remains short exact after -⊗ B
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, both in the same universe, and let $A$ and $B$ be $k$-linear representations of $G$. Write $A_* = \operatorname{ind}$ along the inclusion $\bot \hookrightarrow G$ of the restriction of $A$ to the trivial subgroup, and let $\pi_A \colon A_* \to A$ be the canonical map [`Rep.indBotπ`](def/GroupCohomology_TateDimensionShift.html#L27). The short complex `A.dimShiftDown` has as its terms the subrepresentation of $A_*$ carried by $\ker(\pi_A)$ (a subrepresentation because $\pi_A$ is $G$-equivariant), then $A_*$, then $A$; its first map is the inclusion of that kernel submodule and its second map is $\pi_A$, the composite being zero since elements of the kernel map to zero. The assertion is that the image of this short complex under the monoidal functor $\operatorname{tensorRight} B = (-) \otimes B$ on $\mathrm{Rep}\,k\,G$, namely $$0 \to \ker(\pi_A)\otimes B \to A_*\otimes B \to A\otimes B \to 0,$$ is short exact in the sense of Mathlib's `ShortComplex.ShortExact`: the first map is a monomorphism, the second an epimorphism, and the complex is exact at the middle term.
--
--   This is the first-variable dimension-shifting sequence of Tate cohomology, tensored with a fixed representation $B$; it is the sequence along which the Tate cup product is shifted in its first argument. It is used in establishing associativity and commutativity of the Tate cup product and the comparison of the cup product with the shift maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_dimShiftDown_map_tensorRight.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.shortExact_dimShiftDown_map_tensorRight {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    (A.dimShiftDown.map (MonoidalCategory.tensorRight B)).ShortExact := by sorry
