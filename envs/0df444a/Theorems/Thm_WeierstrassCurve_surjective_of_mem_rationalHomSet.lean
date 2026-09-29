-- Prove2me | Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
-- name    : WeierstrassCurve.surjective_of_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/a78cfa46-885f-5acd-8fed-e1deca0ce46e
-- title:
--   Nonzero rational homomorphisms of elliptic curves are surjective
-- statement:
--   Let $F$ be a field, let $k$ be an algebraically closed field equipped with an $F$-algebra structure, and let $W_1, W_2$ be Weierstrass curves over $F$ which are elliptic (non-vanishing discriminant). Write $W_i(k)$ for the group of affine points, in the Mathlib sense, of the base change of $W_i$ to $k$, so points are the point at infinity together with pairs $(x,y)$ satisfying the Weierstrass equation and nonsingularity. Let $\alpha : W_1(k) \to W_2(k)$ be a homomorphism of additive groups lying in [`WeierstrassCurve.rationalHomSet k W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28), that is, either $\alpha = 0$ or $\alpha$ is rationally represented over $F$: there exist bivariate polynomials $n_X, d_X, n_Y, d_Y \in F[X][Y]$ and a finite set $B \subseteq k$ such that for every $x, y \in k$ with $(x,y)$ a nonsingular point of the base change of $W_1$ and $x \notin B$, the values of $d_X$ and $d_Y$ at $(x,y)$ (after base change to $k$) are nonzero and $\alpha$ sends $(x,y)$ to the point with coordinates $n_X(x,y)/d_X(x,y)$ and $n_Y(x,y)/d_Y(x,y)$. Assume further $\alpha \neq 0$. Then $\alpha$ is surjective as a function: every point of $W_2(k)$ lies in its image.
--
--   This is the statement that a non-constant isogeny of elliptic curves is surjective on points over an algebraically closed field, expressed in the formalisation's currency of homomorphisms given by rational functions with coefficients in the base field $F$. It is used throughout the quaternionic and Čerednik–Drinfel'd material, where surjectivity of nonzero rational homomorphisms underlies the identification of quotients of point groups and of kernels of ideals in rational endomorphism rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.surjective_of_mem_rationalHomSet {F : Type*} [Field F] (k : Type*)
    [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) :
    Function.Surjective α := by sorry
