-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange
-- name    : WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/c33d017b-5bac-5732-8bc9-4d558fd3848e
-- title:
--   Homomorphisms of elliptic curves do not grow under algebraically closed extensions
-- statement:
--   Let $k$ be an algebraically closed field of characteristic zero and $K$ an algebraically closed field that is a $k$-algebra, both equipped with decidable equality, and let $W_1, W_2$ be Weierstrass curves over $k$ satisfying `IsElliptic`. Let $\beta$ be an additive map from the group of affine points of $W_1 \otimes_k K$ to that of $W_2 \otimes_k K$ which lies in [`WeierstrassCurve.rationalHomSet K (W₁.baseChange K) (W₂.baseChange K)`](def/WeierstrassCurve_RationalEnd.html#L28), i.e. either $\beta = 0$, or there are four bivariate polynomials $n_X, d_X, n_Y, d_Y$ with coefficients in $K$ and a finite set $B \subseteq K$ such that for every nonsingular affine point $(x,y)$ of $W_1 \otimes_k K$ with $x \notin B$ the values of $d_X$ and $d_Y$ at $(x,y)$ are nonzero and $\beta$ sends $(x,y)$ to the point with coordinates $(n_X/d_X)(x,y)$, $(n_Y/d_Y)(x,y)$. The conclusion is that there exists an additive map $\beta_0$ between the affine point groups of $W_1 \otimes_k k$ and $W_2 \otimes_k k$ lying in [`WeierstrassCurve.rationalHomSet k W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28) — so either zero, or given off a finite set of abscissae in $k$ by such a quadruple of polynomials with coefficients in $k$ — with $\beta(\iota P) = \iota(\beta_0 P)$ for every point $P$, where $\iota$ denotes `WeierstrassCurve.Affine.Point.map` along the algebra map $k \to K$.
--
--   This is the surjectivity half of the Lefschetz-principle statement $\mathrm{Hom}_k(W_1,W_2) = \mathrm{Hom}_K(W_1 \otimes K, W_2 \otimes K)$ for an extension of algebraically closed fields of characteristic zero: every homomorphism between the base-changed curves is already defined over the smaller field. It is invoked in the construction of nonzero rational homomorphisms satisfying a prescribed quadratic relation, and in the descent of rational point homomorphisms to a valuation subring compatible with reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange {k : Type*} (K : Type*) [Field k] [Field K] [CharZero k] [Algebra k K] [IsAlgClosed k] [IsAlgClosed K] [DecidableEq k] [DecidableEq K] (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic] {β : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet K (W₁.baseChange K) (W₂.baseChange K)) : ∃ β₀ ∈ WeierstrassCurve.rationalHomSet k W₁ W₂, ∀ P : (W₁.baseChange k).toAffine.Point, β (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom k k K) P) = WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom k k K) (β₀ P) := by sorry
