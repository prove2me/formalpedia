-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Chart_infinity_ramificationIdx_eq_two
-- name    : WeierstrassCurve.Affine.Chart.infinity_ramificationIdx_eq_two
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T14:09:21.424957+00:00
-- url     : https://prove2.me/theorems/97263166-9cf7-4445-88cb-53616320e61c
-- title:
--   Every place at infinity of a Weierstrass function field has ramification index $2$ over $k(x)$
-- statement:
--   Let $k$ be a field and let $E$ be the Weierstrass curve over $k$
--   $$E:\ y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6\qquad(a_1,\dots,a_6\in k)$$
--   (no nonsingularity assumption: the discriminant may vanish). Let $k[E]=k[x,y]/\big(y^2+a_1xy+a_3y-x^3-a_2x^2-a_4x-a_6\big)$ be its affine coordinate ring and let $K$ be a field of fractions of $k[E]$, viewed as an extension of $k(X)$ through $X\mapsto x$. The structure maps $k[X]\to k[E]\to K$ and $k[X]\to k(X)\to K$ are assumed compatible, and $K$ is assumed finite and separable over $k(X)$ (these are hypotheses of the statement). No assumption is made on the constant field of $K$.
--
--   Let $\mathcal O_\infty=\{f\in k(x):\deg f\le0\}$ be the valuation ring at infinity of $k(x)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$), a discrete valuation ring with maximal ideal $\mathfrak m_\infty=(1/x)$, and let $\mathcal O_{K,\infty}$ be the integral closure of $\mathcal O_\infty$ in $K$, a Dedekind domain. Its nonzero prime ideals $\mathfrak P$ all lie over $\mathfrak m_\infty$ and correspond to the places of $K$ above the infinite place of $k(x)$. Then for every nonzero prime ideal $\mathfrak P$ of $\mathcal O_{K,\infty}$ the ramification index of $\mathfrak P$ over $\mathfrak m_\infty$ equals two:
--   $$e(\mathfrak P\,|\,\mathfrak m_\infty)=\max\{n\ge0:\ \mathfrak m_\infty\mathcal O_{K,\infty}\subseteq\mathfrak P^{\,n}\}=2 .$$
--
--   Since $K=k(x)\oplus k(x)\,y$ has degree $2$ over $k(x)$, this says that the infinite place of $k(x)$ is totally ramified in $K$; geometrically, $x$ has a double pole at the point $O$ at infinity of the Weierstrass cubic. Combined with the fundamental equality $\sum e\,f=[K:k(x)]$, it yields that there is only one place above infinity and that it has inertia degree one, hence degree one.
--
--   **Formalization Note** `W : WeierstrassCurve.Affine k` is an arbitrary Weierstrass curve: the statement is made with `omit [W.IsElliptic]`, and `include W` makes the curve an explicit argument. The curve enters only through the hypotheses on `K`: `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]`, `IsScalarTower k[X] W.CoordinateRing K`, together with `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, `FunctionField k K` and `Algebra.IsSeparable k⟮X⟯ K`; `IsFullConstantField k K` is not assumed. In the preamble, `A∞` is `inftyValuationSubring k`, the valuation subring of Mathlib's `RatFunc.inftyValuation k`, and `S∞` is `infiniteIntegers k K = integralClosure A∞ K`; the nonzero primes are the elements of `IsDedekindDomain.HeightOneSpectrum S∞`. The local instances of the preamble (the algebra $k\to K$ through $k[X]$ and some scalar-tower and faithfulness facts) are definitions provided by `Def_RiemannRoch_WeierstrassInfinity`, not additional hypotheses. The ramification index is Mathlib's `Ideal.ramificationIdx'`, defined as $\sup\{n:\ \mathfrak m_\infty\mathcal O_{K,\infty}\subseteq\mathfrak P^n\}$.
-- source:
--   Auxiliary lemma of the formalization; no numbered counterpart in the literature. Background: H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 3.1 (ramification index and fundamental equality, cf.) and Section 6.1 (elliptic function fields, cf.); J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009, Sections III.1 and III.3 ($x$ has a pole of order $2$ at $O$, cf.). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/EllipticCurve/Infinity.lean#L240-L263

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

theorem WeierstrassCurve.Affine.Chart.infinity_ramificationIdx_eq_two
    (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    (IsLocalRing.maximalIdeal A∞).ramificationIdx' v.asIdeal = 2 := by sorry
