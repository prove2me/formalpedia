-- Prove2me | Theorems.Thm_Rep_shortExact_dimShiftDownSC_map_tensorRight
-- name    : Rep.shortExact_dimShiftDownSC_map_tensorRight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/a461b385-e8b6-53ad-92ef-8cc74e01d677
-- title:
--   Dimension shift down preserves ⊗ B-short exactness
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in $\mathrm{Rep}_k(G)$, and let $B$ be a representation in $\mathrm{Rep}_k(G)$. Assume that the short complex obtained from $X$ by applying the functor $\mathrm{tensorRight}\,B$, i.e. $- \otimes B$, is short exact (so $f \otimes 1_B$ is a monomorphism, $g \otimes 1_B$ an epimorphism, and the resulting three-term complex is exact). The conclusion is that $(\mathrm{dimShiftDownSC}\,X) \otimes B$ is again short exact. Here, for a representation $A$, $A.\mathrm{indBot}$ denotes $\mathrm{Ind}_{1}^{G}\,\mathrm{Res}_{1}\,A$ and $A.\mathrm{dimShiftDownObj}$ the kernel subrepresentation of the canonical map $\mathrm{indBot}\pi_A : A.\mathrm{indBot} \to A$; [`Rep.dimShiftDownSC X`](def/GroupCohomology_TateDimensionShiftMaps.html#L62) is the short complex whose objects are the $X_i.\mathrm{dimShiftDownObj}$ and whose maps are the restrictions to these kernels of the induced maps $\mathrm{Ind}_{1}^{G}\,\mathrm{Res}_{1}$ applied to $f$ and $g$, the composite of which vanishes. No exactness hypothesis on $X$ itself is imposed.
--
--   This is the downward dimension-shifting step for Tate cohomology, transported through a tensor product with a fixed coefficient representation $B$: exactness of $X \otimes B$ is inherited by the complex of kernels of the induction-counit maps tensored with $B$. It is used in the construction of Tate cup products, via [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_dimShiftDownSC_map_tensorRight.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.shortExact_dimShiftDownSC_map_tensorRight {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (B : Rep.{u} k G)
    (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact) :
    ((Rep.dimShiftDownSC X).map (MonoidalCategory.tensorRight B)).ShortExact := by sorry
