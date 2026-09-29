-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_cup_comm
-- name    : Rep.IsTateCupProduct.cup_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/8021ddc6-b035-507a-9012-d02ee535b637
-- title:
--   Graded commutativity of the Tate cup product
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group, and let $\mathrm{cup}$ be a [`Rep.TateCupFamily k G`](def/GroupCohomology_IsTateCupProduct.html#L20), that is, an assignment to each pair of $k$-linear representations $A,B$ of $G$ and each triple of integers $p,q,r$ with $p+q=r$ of a $k$-bilinear map $\hat H^p(G,A)\times\hat H^q(G,B)\to\hat H^r(G,A\otimes B)$, where $\hat H^n$ denotes [`Rep.tateCohomology`](def/GroupCohomology_TateCohomology.html#L140): group cohomology in degrees $n\ge 1$, the invariants modulo the image of the norm map in degree $0$, the kernel of the norm map in degree $-1$, and group homology in degrees $n\le -2$. Assume `hcup : Rep.IsTateCupProduct cup`, i.e. that this family agrees with any graded cup product on group cohomology in bidegrees $(p+1,q+1)$, is natural in both variables under [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17) of a tensor product of morphisms, and is compatible with the Tate connecting maps of short exact sequences in the first variable (without sign) and in the second variable (with the sign $(-1)^p$). Then for all $A,B$, all integers $p,q,r$ with $p+q=r$, and all $x\in\hat H^p(G,A)$, $y\in\hat H^q(G,B)$, the class $\mathrm{cup}\,B\,A\,q\,p\,r\,y\,x$ equals $(-1)^{pq}$, cast from $\mathbb{Z}$ into $k$, times the image of $\mathrm{cup}\,A\,B\,p\,q\,r\,x\,y$ under the map induced in degree $r$ by the braiding $\beta_{A,B}\colon A\otimes B\to B\otimes A$.
--
--   This is the graded (anti)commutativity of the cup product on the Tate cohomology of a finite group, stated axiomatically for any family of pairings satisfying the characterising properties of [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28). It is used in the construction and vanishing statements for the Tate–Nakayama pairing, where it transfers results about the pairing in one variable to the other.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_cup_comm.lean

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

theorem Rep.IsTateCupProduct.cup_comm {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (p q r : ℤ) (h : p + q = r) (x : A.tateCohomology p) (y : B.tateCohomology q) :
    cup B A q p r (by omega) y x
      = (((p * q).negOnePow : ℤ) : k) • (Rep.tateMap (β_ A B).hom r).hom (cup A B p q r h x y) := by sorry
