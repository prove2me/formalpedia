-- Prove2me | Theorems.Thm_Rep_indBotSC_shortExact
-- name    : Rep.indBotSC_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/a989e8d0-4844-5cd6-aea6-7804c3720417
-- title:
--   Induction from the trivial subgroup preserves short exactness
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$ (so $f$ followed by $g$ is zero). Assume $X$ is short exact, that is, $f$ is a monomorphism, $g$ is an epimorphism and the complex is exact at the middle term. The conclusion is that the short complex [`Rep.indBotSC X`](def/GroupCohomology_TateDimensionShiftMaps.html#L56) is again short exact. Here, for a morphism $\varphi$ of representations, [`Rep.indBotMap`](def/GroupCohomology_TateDimensionShiftMaps.html#L17) $\varphi$ is obtained by restricting $\varphi$ along the inclusion of the trivial subgroup $\bot \le G$ and then applying the induction functor `Rep.indFunctor` for that inclusion; [`Rep.indBotSC X`](def/GroupCohomology_TateDimensionShiftMaps.html#L56) is the short complex whose two maps are [`Rep.indBotMap X.f`](def/GroupCohomology_TateDimensionShiftMaps.html#L17) and [`Rep.indBotMap X.g`](def/GroupCohomology_TateDimensionShiftMaps.html#L17), its vanishing composite coming from functoriality of restriction and induction together with $X.f \gg X.g = 0$. Thus induction from the trivial subgroup, applied termwise, carries short exact sequences of $G$-representations to short exact sequences.
--
--   This is the exactness of the functor $A \mapsto \mathrm{Ind}_1^G(\mathrm{Res}_1 A)$, which over $k$ is the functor $A \mapsto k[G] \otimes_k A$ with $k[G]$ free; it is the input needed to embed a representation into an induced (hence cohomologically trivial) one. It is used in the construction of dimension-shifting maps for Tate cohomology, and is cited by [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_indBotSC_shortExact.lean

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

theorem Rep.indBotSC_shortExact {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep.{u} k G)}
    (hX : X.ShortExact) : (Rep.indBotSC X).ShortExact := by sorry
