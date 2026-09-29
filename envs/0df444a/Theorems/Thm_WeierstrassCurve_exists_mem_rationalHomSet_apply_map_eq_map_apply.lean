-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply
-- name    : WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/d69b3c58-16fb-5528-8d52-bf2c42e1947c
-- title:
--   Rational homomorphisms extend from k₀-points to k-points
-- statement:
--   Let $F$ be a field and let $k_0$, $k$ be fields equipped with $F$-algebra structures together with a $k_0$-algebra structure on $k$ forming a scalar tower over $F$, with $k_0$ algebraically closed. Let $W_1$, $W_2$ be Weierstrass curves over $F$, both elliptic. Let $\alpha_0$ be an additive map from the group of points of the affine model of the base change $W_1 \!\times_F\! k_0$ to that of $W_2 \!\times_F\! k_0$ which lies in [`WeierstrassCurve.rationalHomSet k₀ W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28), that is: either $\alpha_0 = 0$, or there are four bivariate polynomials $n_X, d_X, n_Y, d_Y \in F[X][Y]$ and a finite set $B \subseteq k_0$ such that for all $x, y \in k_0$ with $(x,y)$ a nonsingular point of the affine curve $W_1 \!\times_F\! k_0$ and $x \notin B$, the base-changed evaluations of $d_X$ and $d_Y$ at $(x,y)$ are nonzero and $\alpha_0$ sends the affine point $(x,y)$ to the affine point with coordinates $n_X(x,y)/d_X(x,y)$ and $n_Y(x,y)/d_Y(x,y)$. The conclusion asserts the existence of an additive map $\alpha$ on the points over $k$ satisfying the same disjunction over $k$ (zero, or represented by polynomials over $F$ outside a finite subset of $k$), and such that for every point $P$ of $W_1 \!\times_F\! k_0$ one has $\alpha(\iota_* P) = \iota_*(\alpha_0 P)$, where $\iota_*$ denotes the map on affine points induced by the $F$-algebra homomorphism $k_0 \to k$.
--
--   This is the base-change compatibility for $F$-rational homomorphisms of elliptic curves: a homomorphism of groups of points given by fixed rational functions with coefficients in $F$, read over an algebraically closed field $k_0 \supseteq F$, is realised by the same data over any field extension $k$ of $k_0$, compatibly with the inclusion of points. It is used in the constructions of rational endomorphisms, for instance in producing elements of [`WeierstrassCurve.rationalHomSet`](def/WeierstrassCurve_RationalEnd.html#L28) satisfying prescribed algebraic relations over larger fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply {F : Type*} [Field F] (k₀ : Type*) (k : Type*) [Field k₀] [Field k] [Algebra F k₀] [Algebra F k] [Algebra k₀ k] [IsScalarTower F k₀ k] [IsAlgClosed k₀] [DecidableEq k₀] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {α₀ : (W₁⁄k₀).Point →+ (W₂⁄k₀).Point} (hα₀ : α₀ ∈ WeierstrassCurve.rationalHomSet k₀ W₁ W₂) : ∃ α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂, ∀ P : (W₁⁄k₀).Point, α (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom F k₀ k) P) = WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom F k₀ k) (α₀ P) := by sorry
