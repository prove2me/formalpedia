-- Prove2me | Theorems.Thm_WeierstrassCurve_neg_mem_rationalHomSet
-- name    : WeierstrassCurve.neg_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/580839d4-da14-5196-9d8d-0457a16f80be
-- title:
--   Negation preserves rationally represented homomorphisms
-- statement:
--   Let $F$ and $k$ be fields with $k$ an $F$-algebra, and let $W_1,W_2$ be Weierstrass curves over $F$. Write $W_i(k)$ for the group of affine points of the base change of $W_i$ to $k$ (the point type of `(Wᵢ.baseChange k).toAffine`), and let $\alpha\colon W_1(k)\to W_2(k)$ be an additive monoid homomorphism. The set [`WeierstrassCurve.rationalHomSet k W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28) consists of those $\alpha$ which are either the zero homomorphism or are rationally represented, i.e. for which there exist bivariate polynomials $n_X,d_X,n_Y,d_Y \in F[X][Y]$ and a finite set $B\subseteq k$ such that for every pair $(x,y)$ of elements of $k$ satisfying the nonsingularity condition for the base-changed affine equation with $x\notin B$, the values at $(x,y)$ of the images of $d_X$ and $d_Y$ under the coefficientwise map $F\to k$ are nonzero and $\alpha$ sends the affine point $(x,y)$ to the affine point with coordinates $n_X(x,y)/d_X(x,y)$ and $n_Y(x,y)/d_Y(x,y)$ (in particular this pair is again nonsingular). The theorem asserts that if $\alpha$ lies in this set, so does $-\alpha$.
--
--   This records that the set of rationally represented homomorphisms between groups of $k$-points of Weierstrass curves is closed under negation, the negation being that of the group of points of $W_2$, given by $-(u,v)=(u,-v-a_1u-a_3)$. Together with closure under addition, composition and the presence of $0$, it makes the rational homomorphism sets stable under the ring operations, and it is used in the Čerednik–Drinfeld part of the development, where kernel ideals are formed from rational homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_neg_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.neg_mem_rationalHomSet
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]
    (W₁ W₂ : WeierstrassCurve F)
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) :
    -α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂ := by sorry
