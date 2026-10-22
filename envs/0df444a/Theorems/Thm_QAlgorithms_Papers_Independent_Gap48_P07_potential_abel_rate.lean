-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_potential_abel_rate
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.potential_abel_rate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:22:04.550341+00:00
-- url     : https://prove2.me/theorems/bdfd0ca8-61c8-45d5-97a7-7034ddc0b42d
-- title:
--   Theorem 4.4.
-- statement:
--   Let $\mu$ be a positive Laplace-transformable Radon measure on $[0,\infty)$ and let $f=\mathcal L\mu=1/g$ be a potential, where $g$ is a nonzero Bernstein function. Suppose $f(t)\to+\infty$ as $t\downarrow0$. Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space $X$. If the genuine damped vector integrals for $x\in X$ converge weakly to $y$, then
--   $$y\in\operatorname{dom}g(A),\quad x=g(A)y,\quad\|C_t(A)x\|=O\!\left(\frac1{f(1/t)}\right).$$
--   If additionally $t/f(1/t)\to\infty$, the last bound is little-o. No global mean ergodicity is assumed. This converts weak Abel summability into quantitative Cesaro decay.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 18, Theorem 4.4.

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

/-- PDF pp.18–19, Theorem 4.4: potential f=1/g, with f(0+)=infinity;
no global mean ergodicity. g is the reciprocal prescribed by f. -/
theorem potential_abel_rate (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T)
    (m : LaplaceRadon) (hpos : ∀ᵐ s ∂m.variation, m.phase s = 1)
    (g : BernsteinData) (hg : NonzeroBernstein g)
    (hpotential : ∀ z : ℂ, 0 < z.re → radonLaplace m z = (bernsteinValue g z)⁻¹)
    (hinf : Tendsto (fun t : ℝ => (radonLaplace m (t : ℂ)).re) (𝓝[>] 0) atTop)
    (x y : X) (hxy : WeakAbel T m x y) :
    (y, x) ∈ hpGraph T (bernsteinValue g) ∧
    Asymptotics.IsBigO atTop (fun t => ‖continuousCesaro T t x‖)
      (fun t : ℝ => 1 / (radonLaplace m ((1 / t : ℝ) : ℂ)).re) ∧
    (Tendsto (fun t : ℝ => t / (radonLaplace m ((1 / t : ℝ) : ℂ)).re) atTop atTop →
      Asymptotics.IsLittleO atTop (fun t => ‖continuousCesaro T t x‖)
        (fun t : ℝ => 1 / (radonLaplace m ((1 / t : ℝ) : ℂ)).re)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
