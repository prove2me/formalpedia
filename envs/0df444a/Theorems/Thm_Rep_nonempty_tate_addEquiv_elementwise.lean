-- Prove2me | Theorems.Thm_Rep_nonempty_tate_addEquiv_elementwise
-- name    : Rep.nonempty_tate_addEquiv_elementwise
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/9a1aa6bd-0fda-5868-a5ec-05d9cd541e1a
-- title:
--   Tate ̂ H⁰ and ̂ H⁻¹ of a cyclic group, elementwise
-- statement:
--   Let $G$ be a finite group acting on a commutative group $M$, written multiplicatively, by group automorphisms (a `MulDistribMulAction`), and let $g \in G$ be an element all of whose integral powers exhaust $G$, i.e. every $x \in G$ lies in `Subgroup.zpowers g`, so $G$ is cyclic with generator $g$. Let $D, N \colon M \to M$ be group homomorphisms satisfying the pointwise descriptions $D(x) = (g \cdot x)/x$ and $N(x) = \prod_{h \in G} h \cdot x$ for all $x \in M$. Consider the representation `Rep.ofMulDistribMulAction G M` attached to this action. The conclusion is a conjunction of two nonemptiness assertions, i.e. the existence of two additive isomorphisms. First, the group $\hat H^0$ of this representation, defined as the invariants modulo the image of the map `normBar` induced by the norm on coinvariants, is isomorphic as an additive group to the additive group of $\ker D$ modulo the subgroup $\operatorname{im} N \cap \ker D$ (the range of $N$ viewed inside $\ker D$ via `Subgroup.subgroupOf`). Second, $\hat H^{-1}$, defined as the kernel of `normBar`, is isomorphic as an additive group to the additive group of $\ker N$ modulo $\operatorname{im} D \cap \ker N$. Only the existence of such isomorphisms is asserted; no particular map is named.
--
--   This is the standard identification, for a cyclic group, of the Tate cohomology groups in degrees $0$ and $-1$ with the elementwise norm-index quotients $\ker(g-1)/NM$ and $\ker N/(g-1)M$. It is the form in which the idèle-class and local-unit computations are phrased, and it is used in the Herbrand-quotient computation for the idèle class group and in the computations of unit cohomology attached to decompositions of places of a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_tate_addEquiv_elementwise.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.nonempty_tate_addEquiv_elementwise
    {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (D N : M →* M)
    (hD : ∀ x, D x = g • x / x) (hN : ∀ x, N x = ∏ h : G, h • x) :
    Nonempty ((Rep.ofMulDistribMulAction G M).tateH0 ≃+ Additive (D.ker ⧸ N.range.subgroupOf D.ker)) ∧
    Nonempty ((Rep.ofMulDistribMulAction G M).tateHneg1 ≃+ Additive (N.ker ⧸ D.range.subgroupOf N.ker)) := by sorry
