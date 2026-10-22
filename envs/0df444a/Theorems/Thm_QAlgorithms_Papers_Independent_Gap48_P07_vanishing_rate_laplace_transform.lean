-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_vanishing_rate_laplace_transform
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.vanishing_rate_laplace_transform
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:27:30.229247+00:00
-- url     : https://prove2.me/theorems/bf48173e-5929-4516-8d71-e87354c76165
-- title:
--   Corollary B.2.
-- statement:
--   Let $g$ be a Bernstein function with rate $r=r[g]$, and suppose both $g(0+)=0$ and $\lim_{t\to\infty}r(t)=0$. For every $\Re z>0$,
--   $$\int_0^\infty e^{-zt}tr(t)\,dt=\frac{g(z)}{z^2},$$
--   with an absolutely integrable integrand. Thus $tr(t)$ is the inverse Laplace transform of $g(z)/z^2$. The zero Bernstein function is allowed.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 26, Corollary B.2.

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

/-- PDF p.26, Corollary B.2: retain both printed zero-limit conditions; g=0 allowed. -/
theorem vanishing_rate_laplace_transform (g : BernsteinData) (ha : g.a = 0)
    (hr : Tendsto (bernsteinRate g) atTop (𝓝 0)) (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * ((t * bernsteinRate g t : ℝ) : ℂ)) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ) * z) * ((t * bernsteinRate g t : ℝ) : ℂ)) =
      bernsteinValue g z / z ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
