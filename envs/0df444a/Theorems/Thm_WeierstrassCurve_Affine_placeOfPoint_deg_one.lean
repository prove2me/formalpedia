-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_deg_one
-- name    : WeierstrassCurve.Affine.placeOfPoint_deg_one
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T14:17:27.096989+00:00
-- url     : https://prove2.me/theorems/d8870035-bc97-46ba-a5dd-94a50d7f1260
-- title:
--   Rational points of an elliptic curve give places of degree one
-- statement:
--   Let $k$ be a field and let $E$ be the Weierstrass curve over $k$
--   $$E:\ y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6\qquad(a_1,\dots,a_6\in k)$$
--   with nonzero discriminant $\Delta$, i.e. an elliptic curve. Let $k[E]=k[x,y]/\big(y^2+a_1xy+a_3y-x^3-a_2x^2-a_4x-a_6\big)$ be its affine coordinate ring and let $K$ be a field of fractions of $k[E]$, viewed as an extension of $k(X)$ through $X\mapsto x$. The structure maps $k\to k[X]\to k[E]\to K$ and $k[X]\to k(X)\to K$ are assumed compatible, and $K$ is assumed finite and separable over $k(X)$ (these are hypotheses of the statement). The structure map $k\to K$ is the composite $k\to k[X]\to K$; no assumption is made on the constant field of $K$.
--
--   The set $E(k)$ of $k$-rational points consists of the point at infinity $O$ together with the affine points $(x_0,y_0)\in k^2$ satisfying the Weierstrass equation at which the curve is nonsingular. To $P\in E(k)$ one attaches a place $\mathfrak p_P$ of $K/k$: for $P=(x_0,y_0)$ it is the place whose valuation ring is the localization of $k[E]$ at the maximal ideal $(x-x_0,\,y-y_0)$, and for $P=O$ it is the place $\infty_K$ of $K$ lying over the infinite place of $k(x)$, i.e. over the valuation ring $\mathcal O_\infty=\{f\in k(x):\deg f\le 0\}$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$).
--
--   The degree of a place $\mathfrak p$ of $K/k$ is $\deg\mathfrak p=[\mathcal O_{\mathfrak p}/\mathfrak m_{\mathfrak p}:k]$, the dimension over $k$ of its residue field. Then for every $P\in E(k)$,
--   $$\deg\mathfrak p_P=1 .$$
--
--   This is one half of the dictionary between the $k$-rational points of an elliptic curve and the places of degree one of its function field, which is used to count points through the zeta function of the function field.
--
--   **Formalization Note** `W : WeierstrassCurve.Affine k` is Mathlib's Weierstrass curve, `W.IsElliptic` means that its discriminant is a unit, and `W.Point` is Mathlib's type of points: `zero` (the point $O$) or an affine point $(x_0,y_0)$ with a proof of `W.Nonsingular x₀ y₀`. The function field is an abstract field `K` with `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]` and `IsScalarTower k[X] W.CoordinateRing K`. The places `placeOfPoint W K P` and `infinityPlace K` are intrinsic places obtained from coordinate places: an affine point gives the height-one prime of the integral closure of $k[X]$ in $K$ corresponding to $(x-x_0,y-y_0)$, and `infinityPlace` comes from a chosen height-one prime of the integral closure in $K$ of the valuation ring at infinity of $k(X)$. The intrinsic places are valuation subrings $\mathcal O\neq K$ containing $k$ with value group order-isomorphic to $\mathbb Z^{m0}$, and the degree `Place.degree` is `Module.finrank k` of the residue field. The instances `FunctionField k K` and `Algebra.IsSeparable k⟮X⟯ K` are hypotheses; `IsFullConstantField k K` is not assumed.
-- source:
--   Auxiliary lemma of the formalization (rational points give places of degree one); no numbered counterpart in the literature. Background: J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009, Section III.1 (Weierstrass equations, the point at infinity $O$). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/EllipticCurve.lean#L47-L50

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

theorem WeierstrassCurve.Affine.placeOfPoint_deg_one (P : W.Point) :
    (placeOfPoint W K P).degree = 1 := by sorry
