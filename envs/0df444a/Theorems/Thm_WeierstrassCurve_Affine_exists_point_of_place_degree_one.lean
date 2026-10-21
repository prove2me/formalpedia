-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_exists_point_of_place_degree_one
-- name    : WeierstrassCurve.Affine.exists_point_of_place_degree_one
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T14:19:53.338987+00:00
-- url     : https://prove2.me/theorems/7be1b2f6-8139-4d45-9e2d-1a045cb44c7d
-- title:
--   Every place of degree one of an elliptic function field comes from a rational point
-- statement:
--   Let $k$ be a field and let $E$ be the Weierstrass curve over $k$
--   $$E:\ y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6\qquad(a_1,\dots,a_6\in k)$$
--   with nonzero discriminant $\Delta$, i.e. an elliptic curve. Let $k[E]=k[x,y]/\big(y^2+a_1xy+a_3y-x^3-a_2x^2-a_4x-a_6\big)$ be its affine coordinate ring and let $K$ be a field of fractions of $k[E]$, viewed as an extension of $k(X)$ through $X\mapsto x$. The structure maps $k\to k[X]\to k[E]\to K$ and $k[X]\to k(X)\to K$ are assumed compatible, and $K$ is assumed finite and separable over $k(X)$ (these are hypotheses of the statement). The structure map $k\to K$ is the composite $k\to k[X]\to K$; no assumption is made on the constant field of $K$.
--
--   The set $E(k)$ of $k$-rational points consists of the point at infinity $O$ together with the affine points $(x_0,y_0)\in k^2$ satisfying the Weierstrass equation at which the curve is nonsingular. To $P\in E(k)$ one attaches a place $\mathfrak p_P$ of $K/k$: for $P=(x_0,y_0)$ it is the place whose valuation ring is the localization of $k[E]$ at the maximal ideal $(x-x_0,\,y-y_0)$, and for $P=O$ it is the place $\infty_K$ of $K$ lying over the infinite place of $k(x)$, i.e. over the valuation ring $\mathcal O_\infty=\{f\in k(x):\deg f\le 0\}$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$).
--
--   Let $v$ be a place of $K/k$ (a valuation ring $\mathcal O_v$ with $k\subseteq\mathcal O_v\subsetneq K$ and infinite cyclic value group) of degree one, i.e. $[\mathcal O_v/\mathfrak m_v:k]=1$. Then there is a rational point $P\in E(k)$ with
--   $$v=\mathfrak p_P .$$
--
--   Together with the fact that each $\mathfrak p_P$ has degree one, this shows that $P\mapsto\mathfrak p_P$ maps $E(k)$ onto the set of places of degree one of $K/k$; in particular, over a finite field $k$, the number of places of degree one is at most $\#E(k)$.
--
--   **Formalization Note** `W : WeierstrassCurve.Affine k` is Mathlib's Weierstrass curve, `W.IsElliptic` means that its discriminant is a unit, and `W.Point` is Mathlib's type of points: `zero` (the point $O$) or an affine point $(x_0,y_0)$ with a proof of `W.Nonsingular x₀ y₀`. The function field is an abstract field `K` with `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]` and `IsScalarTower k[X] W.CoordinateRing K`. The places `placeOfPoint W K P` and `infinityPlace K` are intrinsic places obtained from coordinate places: an affine point gives the height-one prime of the integral closure of $k[X]$ in $K$ corresponding to $(x-x_0,y-y_0)$, and `infinityPlace` comes from a chosen height-one prime of the integral closure in $K$ of the valuation ring at infinity of $k(X)$. The place `v : Place k K` is an intrinsic place (valuation subring with value group order-isomorphic to $\mathbb Z^{m0}$) and `v.degree` is `Module.finrank k` of its residue field. The instances `FunctionField k K` and `Algebra.IsSeparable k⟮X⟯ K` are hypotheses; `IsFullConstantField k K` is not assumed. Only existence of $P$ is asserted (uniqueness is not part of the statement).
-- source:
--   Auxiliary lemma of the formalization (degree-one places are rational points); no numbered counterpart in the literature. Background: J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009, Sections III.1 and III.3. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/EllipticCurve.lean#L75-L84

import Mathlib
import Definitions.Def_RiemannRoch_WeierstrassGenus
/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/

open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc nonZeroDivisors
open WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]
omit [IsFullConstantField k K]
include W

theorem WeierstrassCurve.Affine.exists_point_of_place_degree_one (v : Place k K) (hv : v.degree = 1) :
    ∃ P : W.Point, v = placeOfPoint W K P := by sorry
