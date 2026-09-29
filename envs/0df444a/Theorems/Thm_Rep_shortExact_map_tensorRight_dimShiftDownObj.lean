-- Prove2me | Theorems.Thm_Rep_shortExact_map_tensorRight_dimShiftDownObj
-- name    : Rep.shortExact_map_tensorRight_dimShiftDownObj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/b8be545a-891f-5d00-a9e1-02320b1e15ee
-- title:
--   Dimension-shift subobject preserves tensored short exactness
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $X$ a short complex $X_1 \to X_2 \to X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, and $B$ such a representation. Write $B_* =$ [`Rep.indBot B`](def/GroupCohomology_TateDimensionShift.html#L18) for the induction along the inclusion $\bot \hookrightarrow G$ of the restriction of $B$ to the trivial subgroup, and let `B.dimShiftDownObj` be the subrepresentation of $B_*$ carried by the kernel of the underlying $k$-linear map of the canonical morphism [`Rep.indBotπ B : B.indBot ⟶ B`](def/GroupCohomology_TateDimensionShift.html#L27) (this submodule is $G$-stable, as the definition records). Assume that the short complex obtained from $X$ by applying the functor $-\otimes B$ (`MonoidalCategory.tensorRight B`), namely $X_1\otimes B \to X_2\otimes B \to X_3\otimes B$, is short exact in the sense of Mathlib: its first map is a monomorphism, its second an epimorphism, and it is exact. The conclusion is that the short complex obtained by applying $-\otimes B''$ with $B'' =$ `B.dimShiftDownObj` is likewise short exact. No exactness of $X$ itself is assumed, only of $X\otimes B$.
--
--   This is the dimension-shifting step for the lower shift object $B'' = \ker(B_* \to B)$ attached to a representation $B$: short exactness after tensoring survives replacement of $B$ by $B''$. It feeds the construction of Tate cup products, being cited by [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_map_tensorRight_dimShiftDownObj.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.shortExact_map_tensorRight_dimShiftDownObj {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (B : Rep.{u} k G) (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact) :
    (X.map (MonoidalCategory.tensorRight B.dimShiftDownObj)).ShortExact := by sorry
