-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_weak_abel_extended_calculus
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.weak_abel_extended_calculus
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:14:54.190861+00:00
-- url     : https://prove2.me/theorems/91ab2351-4d0c-4973-9cda-65f00ebc36fa
-- title:
--   Corollary 2.4.
-- statement:
--   Let $\mu$ be a Laplace-transformable complex Radon measure on $[0,\infty)$, $f=\mathcal L\mu$, and let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space $X$. Suppose $x,y\in X$ and the genuine damped integrals converge weakly to $y$ as the positive damping parameter tends to zero. If $g$ is holomorphic and regularizable in this same extended Hille–Phillips calculus and $gf\in A_+^1$, then
--   $$y\in\operatorname{dom}g(A),\qquad (gf)(A)x=g(A)y.$$
--   This conclusion includes new domain membership; it does not assume an auxiliary regularizer from Theorem 2.3 in advance.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 7, Corollary 2.4.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P07

noncomputable section

open Set Filter MeasureTheory

open scoped Topology NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P07

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore graphPower)

open QAlgorithms.Papers.Independent.Renew46.P11
  (LaplaceImage Bernstein CompletelyMonotone SpecialBernstein StieltjesClass PositiveReal)

attribute [local instance] Classical.propDecidable

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- PDF p.7, Corollary 2.4: the new domain conclusion is part of the result. -/
theorem weak_abel_extended_calculus (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T)
    (m : LaplaceRadon) (g : ℂ → ℂ) (hg : HPRegularizable T g)
    (hgf : LaplaceImage (g * radonLaplace m)) (x y : X) (hxy : WeakAbel T m x y) :
    y ∈ graphDomain (hpGraph T g) ∧ (y, hpEval T (g * radonLaplace m) x) ∈ hpGraph T g := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
