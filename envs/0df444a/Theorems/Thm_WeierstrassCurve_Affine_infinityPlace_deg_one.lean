-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_infinityPlace_deg_one
-- name    : WeierstrassCurve.Affine.infinityPlace_deg_one
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T14:18:38.403392+00:00
-- url     : https://prove2.me/theorems/b551278b-caf0-4bfc-95d4-97d96d4decc7
-- title:
--   The place at infinity of a Weierstrass function field has degree one
-- statement:
--   Let $k$ be a field and let $E$ be the Weierstrass curve over $k$
--   $$E:\ y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6\qquad(a_1,\dots,a_6\in k)$$
--   (no nonsingularity assumption: the discriminant may vanish). Let $k[E]=k[x,y]/\big(y^2+a_1xy+a_3y-x^3-a_2x^2-a_4x-a_6\big)$ be its affine coordinate ring and let $K$ be a field of fractions of $k[E]$, viewed as an extension of $k(X)$ through $X\mapsto x$. The structure maps $k\to k[X]\to k[E]\to K$ and $k[X]\to k(X)\to K$ are assumed compatible, and $K$ is assumed finite and separable over $k(X)$ (these are hypotheses of the statement). The structure map $k\to K$ is the composite $k\to k[X]\to K$; no assumption is made on the constant field of $K$.
--
--   Let $\mathcal O_\infty=\{f\in k(x):\deg f\le0\}$ be the valuation ring at infinity of $k(x)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$), and let $\infty_K$ be the place of $K$ given by a (chosen) nonzero prime of the integral closure of $\mathcal O_\infty$ in $K$, i.e. a place of $K$ lying over the infinite place of $k(x)$. Then
--   $$\deg\infty_K=[\mathcal O_{\infty_K}/\mathfrak m_{\infty_K}:k]=1 .$$
--
--   Geometrically, $\infty_K$ corresponds to the point at infinity $O=[0:1:0]$ of the Weierstrass cubic, which is $k$-rational; this is the case $P=O$ of the correspondence between rational points and places of degree one.
--
--   **Formalization Note** `W : WeierstrassCurve.Affine k` is an arbitrary Weierstrass curve (`W.IsElliptic` is omitted). The curve enters only through the hypotheses on `K`: `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]`, `IsScalarTower k[X] W.CoordinateRing K`, together with `FunctionField k K` and `Algebra.IsSeparable k⟮X⟯ K`; `IsFullConstantField k K` is not assumed. `infinityPlace K` is the intrinsic place (valuation subring with value group order-isomorphic to $\mathbb Z^{m0}$) obtained from the coordinate place `Chart.infinityPlace K`, defined by a chosen height-one prime of the integral closure of the valuation ring at infinity; the degree is `Module.finrank k` of its residue field.
-- source:
--   Auxiliary lemma of the formalization; no numbered counterpart in the literature. Background: J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009, Section III.1 (a Weierstrass cubic meets the line at infinity only at $O=[0,1,0]$). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/CoordinateFree/EllipticCurve.lean#L56-L58

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
omit [WeierstrassCurve.IsElliptic W]
omit [IsFullConstantField k K]

theorem WeierstrassCurve.Affine.infinityPlace_deg_one : (infinityPlace (k := k) K).degree = 1 := by sorry
