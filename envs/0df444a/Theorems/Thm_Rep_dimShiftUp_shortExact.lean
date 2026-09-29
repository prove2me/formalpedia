-- Prove2me | Theorems.Thm_Rep_dimShiftUp_shortExact
-- name    : Rep.dimShiftUp_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/5b223856-2c1b-5341-b683-89a638637c3c
-- title:
--   The dimension-shift sequence 0 → A → Ind₁^G A → A_* → 0 is short exact
-- statement:
--   Let $k$ be a commutative ring and $G$ a group with finitely many elements, and let $A$ be a $k$-linear representation of $G$ (an object of `Rep k G`, in a fixed universe). The short complex `A.dimShiftUp` of representations of $G$ is formed as follows: its left term is $A$; its middle term is `A.indBot`, the representation induced along the inclusion $\bot \to G$ of the trivial subgroup from the restriction of $A$ to $\bot$; its right term is `A.dimShiftUpObj`, the quotient of the underlying module of `A.indBot` by the image of the $k$-linear map underlying the morphism `indBotι A`, equipped with the induced $G$-action (the image is $G$-stable because `indBotι A` commutes with the actions); its first map is `indBotι A` and its second map is the canonical quotient map `Submodule.mkQ`, the composite being zero since every element of $A$ maps into the submodule divided out. The assertion is that this short complex is short exact in the sense of Mathlib's `ShortComplex.ShortExact`: `indBotι A` is a monomorphism, the quotient map is an epimorphism, and the complex is exact at its middle term.
--
--   This is the short exact sequence underlying the "injective" half of dimension shifting in the Tate cohomology of a finite group, embedding an arbitrary representation into one induced from the trivial subgroup. It is used in the construction and verification of the Tate cup product, being cited by the associativity, commutativity and character-duality statements for that product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_dimShiftUp_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.dimShiftUp_shortExact {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) :
    (A.dimShiftUp).ShortExact := by sorry
