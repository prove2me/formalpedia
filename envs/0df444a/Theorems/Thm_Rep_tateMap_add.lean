-- Prove2me | Theorems.Thm_Rep_tateMap_add
-- name    : Rep.tateMap_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e3060a25-40ac-54f1-bc7c-e9010ea577ba
-- title:
--   Additivity of the Tate cohomology maps in the morphism
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group, and $A, B$ two $k$-linear representations of $G$ (objects of `Rep k G`). For morphisms $\varphi, \psi : A \to B$ of representations and any integer $n$, the map $\mathrm{Rep.tateMap}(\varphi + \psi)\,n$ on the degree-$n$ Tate cohomology modules coincides with $\mathrm{Rep.tateMap}\,\varphi\,n + \mathrm{Rep.tateMap}\,\psi\,n$, the sum being taken in the additive group of morphisms $A.\mathrm{tateCohomology}\,n \to B.\mathrm{tateCohomology}\,n$ of $k$-modules. Here the Tate groups and the induced maps are given by the four-regime definition: for $n = m+1 > 0$ they are the ordinary group cohomology $H^{m+1}(G, -)$ with the functorial map along the identity of $G$; for $n = 0$ the module is the quotient of the invariants $A^G$ by the image of the norm map $\mathrm{normBar}$, with induced map obtained from the map on invariants by passing to the quotient; for $n = -1$ the module is the kernel of the induced norm map on the coinvariants $A_G$, with induced map the restriction of the map on coinvariants; and for $n = -(m+2)$ it is the group homology $H_{m+1}(G, -)$ with the functorial map along the identity of $G$. Thus $\hat H^n(G, -)$ is additive on morphisms in every integer degree.
--
--   Together with the identity and composition laws for [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17), this is the statement that Tate cohomology $\hat H^n(G, -)$ is an additive functor on $k$-linear representations of a finite group. It is used in the vanishing criterion [`Rep.isZero_tateCohomology_of_bijective_card_nsmul`](thm.html#Rep.isZero_tateCohomology_of_bijective_card_nsmul) and in [`Rep.tateMap_tateDelta_add_tateMap_tateDelta_eq_zero`](thm.html#Rep.tateMap_tateDelta_add_tateMap_tateDelta_eq_zero), the compatibility of the Tate connecting maps with sums of morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_tateMap_add.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.tateMap_add {k G : Type u} [CommRing k] [Group G] [Fintype G] {A B : Rep.{u} k G}
    (φ ψ : A ⟶ B) (n : ℤ) : Rep.tateMap (φ + ψ) n = Rep.tateMap φ n + Rep.tateMap ψ n := by sorry
