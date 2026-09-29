-- Prove2me | Theorems.Thm_Rep_natCard_tateCohomology_zero_and_neg_one_of_isCyclic
-- name    : Rep.natCard_tateCohomology_zero_and_neg_one_of_isCyclic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/5410a04d-f93c-5148-94c3-6afb5bd2591c
-- title:
--   Tate degrees 0 and -1 match H² and H¹ for cyclic G
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite cyclic group (both in the same universe $u$), and let $A$ be an object of `Rep k G`, i.e. a $k$-linear representation of $G$. The theorem asserts a conjunction of two equalities of natural-number cardinalities, taken with `Nat.card` of the underlying types, so that each side is $0$ when the type in question is infinite. First, the cardinality of $A$'s Tate group in degree $0$ equals that of $H^2(G,A)$; here the degree-$0$ Tate group is, by definition, the quotient of the invariants of $A.\rho$ by the range of the $k$-linear map `normBar` attached to $A.\rho$ (the map playing the role of the norm $\sum_{g\in G}g$), viewed as a $k$-module. Second, the cardinality of $A$'s Tate group in degree $-1$, defined as the kernel of that same map `normBar`, equals the cardinality of $H^1(G,A)$. Group cohomology here is Mathlib's `groupCohomology`, and the indexing convention is that in positive degrees the Tate functor is defined to be group cohomology and in degrees $\le -2$ group homology.
--
--   This is the standard two-periodicity comparison for Tate cohomology of a finite cyclic group, in the shape that identifies the Herbrand quotient $|\hat H^0|/|\hat H^{-1}|$ with the quotient $|H^2|/|H^1|$. It is used in the computations of the cohomology of the idele class group for cyclic extensions and in the Herbrand-quotient arguments built on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_natCard_tateCohomology_zero_and_neg_one_of_isCyclic.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.natCard_tateCohomology_zero_and_neg_one_of_isCyclic {k G : Type u} [CommRing k] [Group G] [Fintype G]
    [IsCyclic G] (A : Rep.{u} k G) :
    Nat.card (A.tateCohomology 0) = Nat.card (groupCohomology A 2) ∧
      Nat.card (A.tateCohomology (-1)) = Nat.card (groupCohomology A 1) := by sorry
