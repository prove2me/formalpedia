-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_weak_abel_calculus
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.weak_abel_calculus
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:14:29.508399+00:00
-- url     : https://prove2.me/theorems/39153a3b-76b2-4a36-a246-44c3d5be9261
-- title:
--   Theorem 2.3.
-- statement:
--   Let $\mu$ be a Laplace-transformable complex Radon measure on $[0,\infty)$ and put $f=\mathcal L\mu$. Let $e\in A_+^1$ satisfy $ef\in A_+^1$. Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space $X$. If $x,y\in X$ and the genuine damped vector integrals satisfy
--   $$\mathrm{weak}\!\lim_{\alpha\downarrow0}\int_{[0,\infty)}e^{-\alpha s}T(s)x\,\mu(ds)=y,$$
--   then $(ef)(A)x=e(A)y$. No injectivity of $e(A)$ or $A$, and no regularizability of $f$, is assumed. The result connects Abel summation to the concrete elementary calculus.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 6, Theorem 2.3.

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

/-- PDF p.6, Theorem 2.3: no injectivity of e(A), A, or regularizability of f
is assumed; all damped integrals are genuine. -/
theorem weak_abel_calculus (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T)
    (m : LaplaceRadon) (e : ℂ → ℂ) (he : LaplaceImage e)
    (hef : LaplaceImage (e * radonLaplace m)) (x y : X) (hxy : WeakAbel T m x y) :
    hpEval T (e * radonLaplace m) x = hpEval T e y := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
