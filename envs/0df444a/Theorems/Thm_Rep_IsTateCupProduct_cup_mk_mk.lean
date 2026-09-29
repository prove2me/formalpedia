-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_cup_mk_mk
-- name    : Rep.IsTateCupProduct.cup_mk_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/d700a8cd-e726-5d63-ba60-e80674b342c4
-- title:
--   Cup product of invariant classes in degree (0,0)
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let `cup` be a member of [`Rep.TateCupFamily k G`](def/GroupCohomology_IsTateCupProduct.html#L20), i.e. a family assigning to each pair of representations $A,B$ of $G$ over $k$, each triple of integers $p,q,r$ and each proof that $p+q=r$ a $k$-bilinear map $\hat H^p(A)\times\hat H^q(B)\to\hat H^r(A\otimes B)$ between the Tate cohomology modules, and suppose `hcup` holds: `cup` agrees with any graded cup product on ordinary group cohomology in bidegrees $(p+1,q+1)$, is natural for tensor products of morphisms of representations, and satisfies the two connecting-map identities (the second with sign $(-1)^p$). Let $A,B$ be representations of $G$ over $k$, let $a$ lie in the invariants of $A$, $b$ in the invariants of $B$, and $c$ in the invariants of $A\otimes_k B$, and assume that $c$, viewed in $A\otimes_k B$, equals $a\otimes_k b$. Then the value of `cup` at $A$, $B$ in bidegree $(0,0,0)$, with the proof $0+0=0$, on the class of $a$ and the class of $b$ equals the class of $c$, where in each case the degree-zero Tate cohomology is the quotient of the invariants by the range of the norm map [`Representation.normBar`](def/GroupCohomology_TateCohomology.html#L40) (induced on coinvariants by the norm $\sum_{g\in G}\rho(g)$) and classes are taken in that quotient.
--
--   This is the standard description of the cup product $\hat H^0(G,A)\times\hat H^0(G,B)\to\hat H^0(G,A\otimes B)$ for a finite group on the level of invariants: the product of the classes of invariant elements $a$ and $b$ is the class of $a\otimes b$. It serves as the base computation from which associativity and graded commutativity of the Tate cup product in low degrees are checked, and is cited by [`Rep.IsTateCupProduct.cup_assoc`](thm.html#Rep.IsTateCupProduct.cup_assoc) and [`Rep.IsTateCupProduct.cup_comm`](thm.html#Rep.IsTateCupProduct.cup_comm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_cup_mk_mk.lean

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

theorem Rep.IsTateCupProduct.cup_mk_mk {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (a : A.ρ.invariants) (b : B.ρ.invariants) (c : (A ⊗ B).ρ.invariants)
    (hc : (c : (A ⊗ B : Rep.{u} k G)) = (a : A) ⊗ₜ[k] (b : B)) :
    cup A B 0 0 0 (add_zero 0) (Submodule.Quotient.mk a : A.tateH0) (Submodule.Quotient.mk b : B.tateH0)
      = (Submodule.Quotient.mk c : (A ⊗ B).tateH0) := by sorry
