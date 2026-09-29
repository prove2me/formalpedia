-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_cup_mk_right_eq_tateMap
-- name    : Rep.IsTateCupProduct.cup_mk_right_eq_tateMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e618ee0e-b769-5e86-b80a-d5e13207d06a
-- title:
--   Cup product with a degree-zero class on the right
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $cup$ be a Tate cup family for $k$ and $G$, that is, an assignment to each pair of $k$-linear $G$-representations $A$, $B$ and each triple of integers $p,q,r$ with $p+q=r$ of a $k$-bilinear map $\hat H^p(G,A)\times\hat H^q(G,B)\to\hat H^r(G,A\otimes_k B)$, where $\hat H^n$ denotes [`Rep.tateCohomology`](def/GroupCohomology_TateCohomology.html#L140) (group cohomology in degrees $\ge 1$, the invariants modulo the image of the norm map $\hat H^0$, the kernel of that norm map in degree $-1$, and group homology in degrees $\le -2$); assume $cup$ satisfies [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28), i.e. it agrees in strictly positive bidegrees with any graded cup product on group cohomology, is natural for morphisms $\varphi\otimes\psi$ via [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17), and interacts with the Tate connecting maps [`Rep.tateδ`](def/GroupCohomology_TateShiftMaps.html#L32) by the two stated rules (no sign in the first variable, the sign $(-1)^p$ in the second). Let $A,B$ be representations, let $b$ be an element of the submodule of $G$-invariants of $B$, let $\psi : A \to A\otimes_k B$ be a morphism of representations whose underlying map sends every $a$ to $a\otimes_k b$, let $p$ be an integer and let $x\in\hat H^p(G,A)$. Then the cup product of $x$ with the class of $b$ in $\hat H^0(G,B)$, formed in degrees $p$ and $0$ with sum $p$, equals the image of $x$ under the map $\hat H^p(G,A)\to\hat H^p(G,A\otimes_k B)$ induced by $\psi$.
--
--   This identifies cup product with a degree-zero Tate class on the right as the functorially induced map, with no sign, and is the right-hand counterpart of the corresponding statement for a degree-zero class on the left. It is used to compute cup products against explicit invariants, in particular in the degree $-1$ computation [`Rep.IsTateCupProduct.cup_neg_one_mk`](thm.html#Rep.IsTateCupProduct.cup_neg_one_mk) and in the lemmas on relation modules and vanishing of connecting maps that follow it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_cup_mk_right_eq_tateMap.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.IsTateCupProduct.cup_mk_right_eq_tateMap {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (b : B.ρ.invariants) (ψ : A ⟶ A ⊗ B) (hψ : ∀ a : A, ψ.hom a = a ⊗ₜ[k] (b : B))
    (p : ℤ) (x : A.tateCohomology p) :
    cup A B p 0 p (add_zero p) x (Submodule.Quotient.mk b : B.tateH0) = (Rep.tateMap ψ p).hom x := by sorry
