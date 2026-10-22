-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_cesaro_bernstein_norm
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.cesaro_bernstein_norm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:18:35.065898+00:00
-- url     : https://prove2.me/theorems/3fccb0eb-b7fb-4b83-8f91-be9e50025156
-- title:
--   Theorem 3.1.
-- statement:
--   Let $g\sim(a,b,\mu)$ be a Bernstein function and, for $t>0$, set $r[g](t)=a/2+b/t+\int_{(0,\infty)}\min(s/t,1)\,\mu(ds)$. Let $C_t(z)=(1-e^{-tz})/(tz)$, with continuous value $C_t(0)=1$. Then
--   $$C_tg\in A_+^1(\mathbb C_+),\qquad \|C_tg\|_{A_+^1}=2r[g](t)\quad(t>0).$$
--   This is equality in the total variation norm of the representing finite complex measure, rather than only an operator norm estimate.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 14, Theorem 3.1.

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

/-- PDF p.14, Theorem 3.1: equality in total-variation Laplace norm. -/
theorem cesaro_bernstein_norm (g : BernsteinData) (t : ℝ) (ht : 0 < t) :
    LaplaceImage (fun z => cesaroSymbol t z * bernsteinValue g z) ∧
    laplaceNorm (fun z => cesaroSymbol t z * bernsteinValue g z) = 2 * bernsteinRate g t := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
