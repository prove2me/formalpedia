-- Prove2me | Theorems.Thm_Rep_indBotPi_indBotMk
-- name    : Rep.indBotPi_indBotMk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/93cbfec5-2b78-55af-ac5c-072a3c26db2b
-- title:
--   The map indBotπ sends [g⊗ a] to g⁻¹a
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $A$ an object of `Rep k G`, i.e. a $k$-linear representation of $G$ on a $k$-module, with action denoted $A.\rho$. Write $A.\mathrm{indBot}$ for the representation `Rep.ind` of the inclusion of the trivial subgroup $\bot \le G$ applied to the restriction `Rep.res` of $A$ along that inclusion, i.e. the representation induced from $A$ viewed as a module over the trivial subgroup; for $g \in G$, `A.indBotMk g` is the $k$-linear map $A \to A.\mathrm{indBot}$ given by `Representation.IndV.mk` for the inclusion $\bot \le G$ at the group element $g$, the generator-forming map written classically as $a \mapsto [g \otimes a]$. Let [`Rep.indBotπ A`](def/GroupCohomology_TateDimensionShift.html#L27) be the morphism of representations from $A.\mathrm{indBot}$ to $A$. The theorem asserts that for every $g \in G$ and every element $a$ of $A$, the underlying $k$-linear map of [`Rep.indBotπ A`](def/GroupCohomology_TateDimensionShift.html#L27) sends `A.indBotMk g a` to $A.\rho\, g^{-1}\, a$; note the inverse on the group element.
--
--   This is the explicit formula on generators for the counit-type morphism $\operatorname{Ind}_1^G \operatorname{Res}_1^G A \to A$ of the induction–restriction adjunction at the trivial subgroup. It is the computational input for the Tate dimension-shifting constructions, and is cited by [`Rep.exists_hom_dimShiftDownObj_trivial_leftRegular`](thm.html#Rep.exists_hom_dimShiftDownObj_trivial_leftRegular) and by [`Rep.nonempty_augShortComplex_iso_dimShiftDown`](thm.html#Rep.nonempty_augShortComplex_iso_dimShiftDown).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_indBotPi_indBotMk.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.indBotPi_indBotMk {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g : G) (a : A) :
    (Rep.indBotπ A).hom (A.indBotMk g a) = A.ρ g⁻¹ a := by sorry
