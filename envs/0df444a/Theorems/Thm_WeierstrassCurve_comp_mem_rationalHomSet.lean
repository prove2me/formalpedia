-- Prove2me | Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
-- name    : WeierstrassCurve.comp_mem_rationalHomSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/fe3c6240-7ff3-59e0-85b6-ee484d392077
-- title:
--   Rationally represented point maps are closed under composition
-- statement:
--   Let $F$ be a field, $k$ a field equipped with an $F$-algebra structure, and let $W_1, W_2, W_3$ be Weierstrass curves over $F$. Let $\alpha$ be an additive map from the group of affine points of the base change $W_1 \times_F k$ to that of $W_2 \times_F k$, and $\beta$ an additive map from the points of $W_2 \times_F k$ to those of $W_3 \times_F k$. Assume $\alpha$ lies in [`WeierstrassCurve.rationalHomSet k W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28) and $\beta$ in [`WeierstrassCurve.rationalHomSet k W₂ W₃`](def/WeierstrassCurve_RationalEnd.html#L28), that is: each of the two maps is either the zero homomorphism or is rationally represented over $F$, meaning that there exist bivariate polynomials $n_X, d_X, n_Y, d_Y \in F[X][Y]$ and a finite subset $B \subseteq k$ such that for every pair $(x,y) \in k^2$ satisfying the affine nonsingularity condition for the base-changed source curve and with $x \notin B$, the values of $d_X$ and $d_Y$ at $(x,y)$ (computed after base change to $k$) are nonzero and the image of the affine point $(x,y)$ is the affine point with coordinates $n_X(x,y)/d_X(x,y)$ and $n_Y(x,y)/d_Y(x,y)$. The conclusion is that the composite $\beta \circ \alpha$, as an additive map from the points of $W_1 \times_F k$ to those of $W_3 \times_F k$, again lies in [`WeierstrassCurve.rationalHomSet k W₁ W₃`](def/WeierstrassCurve_RationalEnd.html#L28).
--
--   This is the composition axiom making rationally represented maps of $k$-points a category, and in particular one of the closure properties showing that the rationally represented endomorphisms of a base-changed Weierstrass curve (together with $0$) form a subring of the endomorphism ring of its group of points. It is used throughout the treatment of quaternionic endomorphism and ideal actions on Weierstrass curves, for instance in the Čerednik–Drinfeld material on moduli places, class sets and Atkin–Lehner automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_comp_mem_rationalHomSet.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.comp_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k] (W₁ W₂ W₃ : WeierstrassCurve F) {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} {β : (W₂.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hβ : β ∈ WeierstrassCurve.rationalHomSet k W₂ W₃) : β.comp α ∈ WeierstrassCurve.rationalHomSet k W₁ W₃ := by sorry
