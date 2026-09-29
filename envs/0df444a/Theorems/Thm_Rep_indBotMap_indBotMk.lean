-- Prove2me | Theorems.Thm_Rep_indBotMap_indBotMk
-- name    : Rep.indBotMap_indBotMk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/889d3643-a928-5bfc-b8e8-b8e908f7bdf3
-- title:
--   Induced map on Ind_{{1}}^G generators
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $A$, $B$ be $k$-linear representations of $G$ (objects of `Rep k G`). For a morphism $\varphi : A \to B$ of representations, an element $g \in G$ and a vector $a \in A$, the assertion concerns the functor $A \mapsto A.\mathrm{indBot}$, which is the induction `Rep.ind` along the inclusion of the trivial subgroup $\bot \le G$ applied to the restriction of $A$ to $\bot$, together with the $k$-linear maps $A.\mathrm{indBotMk}\,g : A \to A.\mathrm{indBot}$ given by `Representation.IndV.mk` for that inclusion and that restricted representation at the element $g$, and the morphism $\mathrm{indBotMap}\,\varphi : A.\mathrm{indBot} \to B.\mathrm{indBot}$, defined as `Rep.indMap` along the same inclusion applied to the image of $\varphi$ under the restriction functor to $\bot$. The conclusion is that the underlying $k$-linear map of $\mathrm{indBotMap}\,\varphi$ carries $A.\mathrm{indBotMk}\,g\,a$ to $B.\mathrm{indBotMk}\,g\,(\varphi\,a)$; informally, $\varphi_*[g \otimes a] = [g \otimes \varphi(a)]$.
--
--   This is the compatibility of induction from the trivial subgroup with morphisms of representations, evaluated on the generators $[g \otimes a]$; it pins down the functorial map $\varphi_*$ on $\mathrm{Ind}_{\{1\}}^G$ completely. It is used in the construction of the short exact sequences underlying dimension shifting for Tate cohomology, as in [`Rep.indBotSC_shortExact`](thm.html#Rep.indBotSC_shortExact), [`Rep.dimShiftDownSC_shortExact`](thm.html#Rep.dimShiftDownSC_shortExact) and [`Rep.shortExact_dimShiftDownSC_map_tensorLeft`](thm.html#Rep.shortExact_dimShiftDownSC_map_tensorLeft).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_indBotMap_indBotMk.lean

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

theorem Rep.indBotMap_indBotMk {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (φ : A ⟶ B) (g : G) (a : A) :
    (Rep.indBotMap φ).hom (A.indBotMk g a) = B.indBotMk g (φ.hom a) := by sorry
