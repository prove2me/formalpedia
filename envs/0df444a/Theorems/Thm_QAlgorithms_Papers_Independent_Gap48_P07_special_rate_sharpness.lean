-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_special_rate_sharpness
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.special_rate_sharpness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:22:28.716291+00:00
-- url     : https://prove2.me/theorems/59a75442-5a0e-4078-922a-aca77f8b3ca6
-- title:
--   Theorem 4.6.
-- statement:
--   Let $g$ be a special Bernstein function with rate $r=r[g]$ and $tr(t)\to\infty$. Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space and suppose nonzero spectral points of $A$ accumulate at zero. For every positive nonincreasing function $\epsilon$ tending to zero, there is a vector $y$ in the actual range of $g(A)$ such that
--   $$\sup_{t\ge1}\frac{\|C_t(A)y\|}{\epsilon(t)r(t)}=+\infty.$$
--   Formally, every real threshold is exceeded at some $t\ge1$. Neither mean ergodicity nor dense range is assumed. This is sharpness against every prescribed vanishing improvement factor.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 20, Theorem 4.6.

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

/-- PDF pp.20–21, Theorem 4.6: every error factor has an actual range witness. -/
theorem special_rate_sharpness (g : BernsteinData)
    (hg : SpecialBernstein (bernsteinValue g))
    (hr : Tendsto (fun t => t * bernsteinRate g t) atTop atTop)
    (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) (hacc : SpectralAccumulation T) :
    SharpRate T (hpGraph T (bernsteinValue g)) (bernsteinRate g) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
