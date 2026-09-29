-- Prove2me | Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
-- name    : WeierstrassCurve.add_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/195173b3-1093-5884-9577-aea6465f601b
-- title:
--   Rationally represented homomorphisms are closed under addition
-- statement:
--   Let $F$ be a field, let $k$ be an algebraically closed field equipped with an $F$-algebra structure, and let $W_1, W_2$ be Weierstrass curves over $F$, each elliptic (invertible discriminant). Write $E_i(k)$ for the group of affine points `(W_i.baseChange k).toAffine.Point`. Call an additive homomorphism $\gamma \colon E_1(k) \to E_2(k)$ *rationally represented over $F$* when there are bivariate polynomials $n_X, d_X, n_Y, d_Y \in F[X][Y]$ and a finite set $B \subseteq k$ such that for all $x, y \in k$ with $(x,y)$ a nonsingular point of $W_1$ base changed to $k$ and $x \notin B$, the evaluations of $d_X$ and $d_Y$ at $(x,y)$ (via the coefficient map $F \to k$) are nonzero and $\gamma$ sends the affine point $(x,y)$ to the affine point with coordinates $n_X(x,y)/d_X(x,y)$ and $n_Y(x,y)/d_Y(x,y)$; the set [`WeierstrassCurve.rationalHomSet k W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28) consists of those $\gamma$ that are either the zero homomorphism or rationally represented over $F$ in this sense. The theorem asserts that for $\alpha, \beta$ additive homomorphisms $E_1(k) \to E_2(k)$ lying in [`WeierstrassCurve.rationalHomSet k W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28), the pointwise sum $\alpha + \beta$ again lies in [`WeierstrassCurve.rationalHomSet k W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28).
--
--   This is the additive closure half of the statement that the $F$-rational homomorphisms between two elliptic curves form a group, read in the concrete model of additive maps on $k$-points given off a finite set of abscissae by quotients of polynomials with coefficients in $F$. It is used throughout the development of endomorphism and homomorphism rings of elliptic curves, in particular in the Čerednik–Drinfeld material on quaternionic ideal classes and rational homomorphism sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_add_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.add_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {α β : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) : α + β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂ := by sorry
