-- Prove2me | Theorems.Thm_Rep_dimShiftDownSC_shortExact
-- name    : Rep.dimShiftDownSC_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/f8c1adde-f014-59cb-bbc0-a6163f1617b5
-- title:
--   Exactness of the dimension-shift-down functor on short exact sequences
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ of $k$-linear representations of $G$. For a representation $A$, write $A.\mathrm{indBot}$ for the induced representation $\mathrm{ind}_{\{1\}}^{G}$ of the restriction of $A$ to the trivial subgroup $\bot \le G$, and write $A.\mathrm{dimShiftDownObj}$ for the subrepresentation of $A.\mathrm{indBot}$ given by the kernel of the underlying linear map of the canonical morphism [`Rep.indBotπ A`](def/GroupCohomology_TateDimensionShift.html#L27) $: A.\mathrm{indBot} \to A$; for a morphism $\varphi : A \to B$, [`Rep.dimShiftDownObjMap`](def/GroupCohomology_TateDimensionShiftMaps.html#L36) is the morphism $A.\mathrm{dimShiftDownObj} \to B.\mathrm{dimShiftDownObj}$ obtained by restricting the induced morphism [`Rep.indBotMap`](def/GroupCohomology_TateDimensionShiftMaps.html#L17) $\varphi$ to these kernels. The short complex [`Rep.dimShiftDownSC X`](def/GroupCohomology_TateDimensionShiftMaps.html#L62) is then $X_1.\mathrm{dimShiftDownObj} \to X_2.\mathrm{dimShiftDownObj} \to X_3.\mathrm{dimShiftDownObj}$ with the maps obtained this way from $f$ and $g$. The assertion is that if $X$ is short exact in $\mathrm{Rep}(k,G)$, that is $f$ is a monomorphism, $g$ an epimorphism and the complex exact at the middle term, then [`Rep.dimShiftDownSC X`](def/GroupCohomology_TateDimensionShiftMaps.html#L62) is short exact as well.
--
--   This is the exactness of the Tate dimension-shifting-down functor $A \mapsto A'' = \ker(\mathrm{ind}_{\{1\}}^{G}\mathrm{res}_{\{1\}}A \to A)$ on short exact sequences of representations, obtained from the exactness of $A \mapsto \mathrm{ind}_{\{1\}}^{G}\mathrm{res}_{\{1\}}A$ together with the given sequence by a nine-lemma argument for the columns $A'' \hookrightarrow \mathrm{ind}_{\{1\}}^{G}\mathrm{res}_{\{1\}}A \twoheadrightarrow A$. It feeds the construction of Tate cup products via [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct), where dimension shifting is used to propagate the construction between degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_dimShiftDownSC_shortExact.lean

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

theorem Rep.dimShiftDownSC_shortExact {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep.{u} k G)}
    (hX : X.ShortExact) : (Rep.dimShiftDownSC X).ShortExact := by sorry
