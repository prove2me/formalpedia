-- Prove2me | Theorems.Thm_Rep_shortExact_indBotSC_map_tensorLeft
-- name    : Rep.shortExact_indBotSC_map_tensorLeft
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/6233ce09-4a0f-5a52-b57e-eafa261de14b
-- title:
--   Tensoring preserves short exactness of the Ind_{bot} shift
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category $\mathrm{Rep}_k(G)$ of $k$-linear representations of $G$, and let $A$ be such a representation. Write $A \otimes -$ for the functor `MonoidalCategory.tensorLeft A`. The hypothesis is that the short complex $A \otimes X_1 \to A \otimes X_2 \to A \otimes X_3$ obtained by applying $A \otimes -$ termwise to $X$ is short exact in Mathlib's sense, i.e. the first map is a monomorphism, the second is an epimorphism, and the complex is exact in the middle. The conclusion is that the same holds after the dimension-shifting operation [`Rep.indBotSC`](def/GroupCohomology_TateDimensionShiftMaps.html#L56): this replaces each term $X_i$ by $\mathrm{Ind}_{\bot}^{G}\,\mathrm{Res}_{\bot}\,X_i$ and each map $\varphi$ by $\mathrm{Ind}$ applied to $\mathrm{Res}_{\bot}\varphi$ (the composite being zero because both functors are additive), and the assertion is that the short complex obtained from [`Rep.indBotSC X`](def/GroupCohomology_TateDimensionShiftMaps.html#L56) by applying $A \otimes -$ termwise is again short exact.
--
--   This is the compatibility, with tensoring by a fixed representation, of the dimension-shifting short exact sequence built from induction from the trivial subgroup, used in the construction of cup products on Tate cohomology; it is invoked in [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_shortExact_indBotSC_map_tensorLeft.lean

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

theorem Rep.shortExact_indBotSC_map_tensorLeft {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (A : Rep.{u} k G) (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    ((Rep.indBotSC X).map (MonoidalCategory.tensorLeft A)).ShortExact := by sorry
