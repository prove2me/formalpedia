-- Prove2me | Theorems.Thm_Rep_nonempty_augShortComplex_iso_dimShiftDown
-- name    : Rep.nonempty_augShortComplex_iso_dimShiftDown
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/972e39c8-62f7-590b-93de-073c5099fc3a
-- title:
--   Augmentation sequence is the dimension-shift sequence of k
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe). The assertion is that the type of isomorphisms of short complexes in $\mathrm{Rep}\,k\,G$ between [`Rep.augShortComplex k G`](def/GroupCohomology_SplittingModule.html#L30) and `(Rep.trivial k G k).dimShiftDown` is nonempty. Here [`Rep.augShortComplex k G`](def/GroupCohomology_SplittingModule.html#L30) is the short complex whose middle term is the left regular representation [`Rep.leftRegularFinsupp k G`](def/Compat_Mathlib430.html#L103) on $G \to_0 k$ (translation action), whose third term is the trivial representation of $G$ on $k$, whose map $g$ is the augmentation `augε k G`, whose first term `augIdeal k G` is the subrepresentation of $G \to_0 k$ carried by the kernel of the augmentation, and whose map $f$ is the inclusion `augIdealι k G`; the composite is zero. For $A =$ `Rep.trivial k G k`, the short complex `A.dimShiftDown` has middle term `A.indBot`, the representation induced along the inclusion of the trivial subgroup $\bot \le G$ from the restriction of $A$ to $\bot$, third term $A$, map $g$ given by `indBotπ A`, first term `A.dimShiftDownObj`, the subrepresentation of `A.indBot` carried by the kernel of `indBotπ A`, and $f$ the inclusion of that submodule; again the composite is zero. Thus the two three-term complexes are isomorphic, termwise and compatibly with the maps, as short complexes of $k$-linear $G$-representations.
--
--   This identifies the augmentation sequence $0 \to I_G \to k[G] \to k \to 0$ with the dimension-shifting sequence attached to the trivial representation, so that results formulated for `dimShiftDownObj` and those formulated for the augmentation ideal may be transferred to one another. It is used in the vanishing of Tate cohomology of the restricted splitting module, [`Rep.isZero_tateCohomology_res_splittingModule`](thm.html#Rep.isZero_tateCohomology_res_splittingModule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_augShortComplex_iso_dimShiftDown.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_SplittingModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.nonempty_augShortComplex_iso_dimShiftDown (k G : Type u) [CommRing k] [Group G] :
    Nonempty (Rep.augShortComplex k G ≅ (Rep.trivial k G k).dimShiftDown) := by sorry
