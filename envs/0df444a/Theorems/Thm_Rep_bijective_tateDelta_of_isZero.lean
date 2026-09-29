-- Prove2me | Theorems.Thm_Rep_bijective_tateDelta_of_isZero
-- name    : Rep.bijective_tateDelta_of_isZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/9594ecd6-7410-5048-8461-e74de670d524
-- title:
--   Bijectivity of the Tate connecting map when the middle term vanishes
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group (both in the same universe), let $X$ be a short complex $X_1 \to X_2 \to X_3$ in the category of $k$-linear representations of $G$, and let `hX` be a proof that $X$ is short exact in the sense of `CategoryTheory.ShortComplex.ShortExact`. Let $n$ be an integer. Assume that the $k$-module $\hat H^{n}(X_2)$ is a zero object, and likewise $\hat H^{n+1}(X_2)$, where $\hat H^{m}(A) =$ `A.tateCohomology m` is by definition the group cohomology $H^{m}(G,A)$ for $m \ge 1$, the quotient $A^{G}/\operatorname{range}(\bar N)$ of the invariants by the range of the map $\bar N$ attached to the norm for $m = 0$, the kernel of $\bar N$ for $m = -1$, and the group homology $H_{-m-1}(G,A)$ for $m \le -2$. Then the underlying $k$-linear map of the connecting morphism [`Rep.tateδ hX n`](def/GroupCohomology_TateShiftMaps.html#L32) associated with the short exact sequence in degree $n$ is bijective as a function.
--
--   This is the map-level form of the standard consequence of the long exact sequence in Tate cohomology: if the middle term of a short exact sequence has vanishing Tate cohomology in two consecutive degrees, the connecting map between the outer terms in those degrees is an isomorphism. It is used in the development of Tate cup products, for instance in the duality and surjectivity statements [`Rep.IsTateCupProduct.bijective_cupEv_dual_left`](thm.html#Rep.IsTateCupProduct.bijective_cupEv_dual_left) and [`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_bijective_tateDelta_of_isZero.lean

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

theorem Rep.bijective_tateDelta_of_isZero {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ)
    (h₀ : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology n))
    (h₁ : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology (n + 1))) :
    Function.Bijective (Rep.tateδ hX n).hom := by sorry
