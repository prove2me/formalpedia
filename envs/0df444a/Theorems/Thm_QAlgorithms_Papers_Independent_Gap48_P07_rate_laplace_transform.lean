-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_rate_laplace_transform
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.rate_laplace_transform
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:26:53.872177+00:00
-- url     : https://prove2.me/theorems/4d06ab9b-09f2-4c42-a9ef-a8e4ff11a2be
-- title:
--   Lemma B.1.
-- statement:
--   Let $g\sim(a,b,\mu)$ be a Bernstein function, let $r=r[g]$, and put $\widetilde r(t)=tr(t)$. For every $\Re z>0$ its Laplace integral is absolutely integrable and
--   $$\mathcal L\widetilde r(z)=\int_0^\infty e^{-zt}tr(t)\,dt=\frac{g(z)-g(0+)/2}{z^2}.$$
--   Here $g(0+)=a$. The half of the constant term is essential, as confirmed by a constant Bernstein function. This identifies the inverse Laplace transform used in Appendix B.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 26, Lemma B.1.

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

/-- PDF p.26, Lemma B.1: numerator g(z)-g(0+)/2, visually checked in the PDF;
the Laplace integral is genuine throughout the open halfplane. -/
theorem rate_laplace_transform (g : BernsteinData) (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * z) * ((t * bernsteinRate g t : ℝ) : ℂ)) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ) * z) * ((t * bernsteinRate g t : ℝ) : ℂ)) =
      (bernsteinValue g z - (g.a : ℂ) / 2) / z ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
