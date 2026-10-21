-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_genus_eq_one
-- name    : WeierstrassCurve.Affine.genus_eq_one
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T14:20:32.314697+00:00
-- url     : https://prove2.me/theorems/af992cd8-b335-441f-bdd8-98179a5f4839
-- title:
--   An elliptic function field has genus one
-- statement:
--   Let $k$ be a field and let $E$ be the Weierstrass curve over $k$
--   $$E:\ y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6\qquad(a_1,\dots,a_6\in k)$$
--   with nonzero discriminant $\Delta$, i.e. an elliptic curve. Let $k[E]=k[x,y]/\big(y^2+a_1xy+a_3y-x^3-a_2x^2-a_4x-a_6\big)$ be its affine coordinate ring and let $K$ be a field of fractions of $k[E]$, viewed as an extension of $k(X)$ through $X\mapsto x$. The structure maps $k\to k[X]\to k[E]\to K$ and $k[X]\to k(X)\to K$ are assumed compatible, and $K$ is assumed finite and separable over $k(X)$ (these are hypotheses of the statement). The structure map $k\to K$ is the composite $k\to k[X]\to K$, and $k$ is assumed to be the full constant field of $K$: every element of $K$ algebraic over $k$ lies in $k$.
--
--   A *place* $P$ of $K/k$ is a valuation ring $\mathcal O_P$ with $k\subseteq\mathcal O_P\subsetneq K$ whose value group is infinite cyclic; $v_P:K^\times\to\mathbb Z$ is its normalized valuation and $\deg P=[\mathcal O_P/\mathfrak m_P:k]$ its degree. A *divisor* is a finite formal sum $D=\sum_P n_P\,P$ with $n_P\in\mathbb Z$, of degree $\deg D=\sum_P n_P\deg P$. Its Riemann–Roch space is
--   $$\mathcal L(D)=\{f\in K:\ f=0\ \text{or}\ v_P(f)\ge -n_P\ \text{for every place } P\},$$
--   a $k$-vector space of dimension $\ell(D)$. The *genus* $g$ of $K/k$ is the largest value of the defect $\deg D+1-\ell(D)$ over all divisors $D$.
--
--   Then the function field of the elliptic curve has genus one:
--   $$g(K/k)=1 .$$
--
--   This is the function-field form of the statement that a smooth Weierstrass cubic is a curve of genus one, i.e. an elliptic curve; combined with the Riemann–Roch theorem it gives $\ell(D)=\deg D$ for every divisor of positive degree.
--
--   **Formalization Note** `W : WeierstrassCurve.Affine k` is Mathlib's Weierstrass curve, `W.IsElliptic` means that its discriminant is a unit, and `W.Point` is Mathlib's type of points: `zero` (the point $O$) or an affine point $(x_0,y_0)$ with a proof of `W.Nonsingular x₀ y₀`. The function field is an abstract field `K` with `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]` and `IsScalarTower k[X] W.CoordinateRing K`. The places `placeOfPoint W K P` and `infinityPlace K` are intrinsic places obtained from coordinate places: an affine point gives the height-one prime of the integral closure of $k[X]$ in $K$ corresponding to $(x-x_0,y-y_0)$, and `infinityPlace` comes from a chosen height-one prime of the integral closure in $K$ of the valuation ring at infinity of $k(X)$. Here `FunctionField k K`, `Algebra.IsSeparable k⟮X⟯ K` and `IsFullConstantField k K` are hypotheses. Places (`FunctionField.Place k K`) are valuation subrings $\mathcal O\neq K$ containing the image of $k$ whose value group admits an order isomorphism with $\mathbb Z^{m0}$ (only its existence is recorded); the normalized valuation is written multiplicatively, $v(f)=e^{-v_P(f)}$, so that $f\in\mathcal L(D)$ reads $v(f)\le e^{n_P}$ for every place. Degrees of places and $\ell(D)$ are `Module.finrank` over $k$, and divisors are finitely supported functions from places to $\mathbb Z$. The genus `FunctionField.genus k K` is defined as the natural-number truncation of the supremum in $\mathbb Z$ of the defects $\deg D+1-\ell(D)$.
-- source:
--   J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009, Proposition III.3.1(c) (a smooth Weierstrass cubic is an elliptic curve, i.e. has genus one). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/EllipticCurve.lean#L88-L89

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
include W

theorem WeierstrassCurve.Affine.genus_eq_one : FunctionField.genus k K = 1 := by sorry
