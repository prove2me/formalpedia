-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_smooth_common_rate_invertible
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.smooth_common_rate_invertible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:26:20.820184+00:00
-- url     : https://prove2.me/theorems/fb6c348a-26cf-4ac4-956c-ee3a26e0afa7
-- title:
--   Theorem A.1.
-- statement:
--   Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space. Suppose a single positive nonincreasing function $\phi(t)\to0$ satisfies
--   $$\|C_t(A)x\|=O(\phi(t))\quad\text{for every }x\in\operatorname{dom}^{\infty}A:=\bigcap_{n\ge0}\operatorname{dom}A^n.$$
--   Then $A$ is invertible, with an everywhere defined bounded inverse. The implicit constant and threshold may depend on $x$; no uniform graph norm estimate is assumed. This shows that smooth-vector membership alone cannot supply a common decaying rate for a noninvertible generator.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 25, Theorem A.1.

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

/-- PDF pp.25–26, Theorem A.1: common rate on smooth vectors, with vectorwise
Big-O constants, rather than a uniform graph norm bound as an assumption. -/
theorem smooth_common_rate_invertible (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T)
    (phi : ℝ → ℝ) (hphi : VanishingFactor phi)
    (hr : ∀ x : X, (∀ n : ℕ, x ∈ graphDomain (graphPower (negativeGenerator T) n)) →
      Asymptotics.IsBigO atTop (fun t => ‖continuousCesaro T t x‖) phi) :
    Bounded (graphInverse (negativeGenerator T)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
