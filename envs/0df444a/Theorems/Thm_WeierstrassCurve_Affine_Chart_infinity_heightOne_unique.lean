-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Chart_infinity_heightOne_unique
-- name    : WeierstrassCurve.Affine.Chart.infinity_heightOne_unique
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T14:10:26.278991+00:00
-- url     : https://prove2.me/theorems/e94b6aaf-4baf-4e85-9a68-e3f22ee04644
-- title:
--   A Weierstrass function field has at most one place above the infinite place of $k(x)$
-- statement:
--   Let $k$ be a field and let $E$ be the Weierstrass curve over $k$
--   $$E:\ y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6\qquad(a_1,\dots,a_6\in k)$$
--   (no nonsingularity assumption: the discriminant may vanish). Let $k[E]=k[x,y]/\big(y^2+a_1xy+a_3y-x^3-a_2x^2-a_4x-a_6\big)$ be its affine coordinate ring and let $K$ be a field of fractions of $k[E]$, viewed as an extension of $k(X)$ through $X\mapsto x$. The structure maps $k[X]\to k[E]\to K$ and $k[X]\to k(X)\to K$ are assumed compatible, and $K$ is assumed finite and separable over $k(X)$ (these are hypotheses of the statement). No assumption is made on the constant field of $K$.
--
--   Let $\mathcal O_\infty=\{f\in k(x):\deg f\le0\}$ be the valuation ring at infinity of $k(x)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$), a discrete valuation ring with maximal ideal $\mathfrak m_\infty=(1/x)$, and let $\mathcal O_{K,\infty}$ be the integral closure of $\mathcal O_\infty$ in $K$, a Dedekind domain. Its nonzero prime ideals $\mathfrak P$ all lie over $\mathfrak m_\infty$ and correspond to the places of $K$ above the infinite place of $k(x)$. Then any two nonzero prime ideals of $\mathcal O_{K,\infty}$ coincide: for all $\mathfrak P,\mathfrak Q\in\operatorname{Spec}^1(\mathcal O_{K,\infty})$,
--   $$\mathfrak P=\mathfrak Q .$$
--
--   In other words, the infinite place of $k(x)$ has at most one extension to $K$; since such a prime always exists (it is the place at infinity $\infty_K$ chosen in `RiemannRoch_WeierstrassInfinity`), the place of $K$ above infinity is unique, corresponding to the single point $O$ at infinity of the Weierstrass cubic. This uniqueness is used to show that every place of degree one comes from a rational point and to count places in the genus computation. Existence is not part of this statement.
--
--   **Formalization Note** `W : WeierstrassCurve.Affine k` is an arbitrary Weierstrass curve: the statement is made with `omit [W.IsElliptic]`, and `include W` makes the curve an explicit argument. The curve enters only through the hypotheses on `K`: `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]`, `IsScalarTower k[X] W.CoordinateRing K`, together with `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, `FunctionField k K` and `Algebra.IsSeparable k⟮X⟯ K`; `IsFullConstantField k K` is not assumed. In the preamble, `A∞` is `inftyValuationSubring k`, the valuation subring of Mathlib's `RatFunc.inftyValuation k`, and `S∞` is `infiniteIntegers k K = integralClosure A∞ K`; the nonzero primes are the elements of `IsDedekindDomain.HeightOneSpectrum S∞`. The local instances of the preamble (the algebra $k\to K$ through $k[X]$ and some scalar-tower and faithfulness facts) are definitions provided by `Def_RiemannRoch_WeierstrassInfinity`, not additional hypotheses.
-- source:
--   Auxiliary lemma of the formalization; no numbered counterpart in the literature. Background: H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 3.1 (extensions of places, fundamental equality, cf.) and Section 6.1 (elliptic function fields, cf.); J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009, Section III.1 (a Weierstrass cubic meets the line at infinity only at $O=[0,1,0]$). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/EllipticCurve/Infinity.lean#L309-L349

import Mathlib
import Definitions.Def_RiemannRoch_WeierstrassInfinity
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
open Polynomial
open scoped Polynomial RatFunc
open WeierstrassCurve.Affine.Chart
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K]
  [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
attribute [local instance] WeierstrassCurve.Affine.Chart.instAlgebraConstants
attribute [local instance] WeierstrassCurve.Affine.Chart.instConstantsTower
attribute [local instance] WeierstrassCurve.Affine.Chart.instCoordinateConstantsTower
local notation "A∞" => inftyValuationSubring k
local notation "S∞" => infiniteIntegers k K
attribute [local instance] WeierstrassCurve.Affine.Chart.instFaithfulInfinity
attribute [local instance] WeierstrassCurve.Affine.Chart.instInfinityConstantsTower
include W
omit [WeierstrassCurve.IsElliptic W]

theorem WeierstrassCurve.Affine.Chart.infinity_heightOne_unique
    (v w : IsDedekindDomain.HeightOneSpectrum S∞) : v = w := by sorry
