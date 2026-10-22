-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_logarithmic_stieltjes
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.logarithmic_stieltjes
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:17:49.543006+00:00
-- url     : https://prove2.me/theorems/616c28e8-4b82-4546-bbe9-d7cd7abf0eeb
-- title:
--   Example 2.9.
-- statement:
--   Let $\log$ denote the principal complex logarithm and define $f(z)=\log z/(z-1)$, with removable value $f(1)=1$. Its restriction to the positive axis is a Stieltjes function. More precisely, for $\Re z>0$ the following integral is absolutely integrable and
--   $$f(z)=\int_0^\infty\frac{dt}{(z+t)(1+t)}.$$
--   This explicit Stieltjes representation also fixes the removable value and supports the logarithmic examples later in the paper.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 11, Example 2.9.

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

/-- PDF pp.11–12, Example 2.9: Stieltjes membership and its explicit integral;
the removable quotient at one is assigned one. -/
theorem logarithmic_stieltjes :
    (fun z : PositiveReal => (logarithmicStieltjes (z.1 : ℂ)).re) ∈ StieltjesClass 1 ∧
    ∀ z : ℂ, 0 < z.re →
      IntegrableOn (fun t : ℝ => ((z + (t : ℂ)) * (1 + (t : ℂ)))⁻¹) (Ioi 0) ∧
      logarithmicStieltjes z = ∫ t in Ioi (0 : ℝ), ((z + (t : ℂ)) * (1 + (t : ℂ)))⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
