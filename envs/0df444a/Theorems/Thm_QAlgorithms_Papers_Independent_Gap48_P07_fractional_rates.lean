-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_fractional_rates
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.fractional_rates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:23:59.755503+00:00
-- url     : https://prove2.me/theorems/daf6f17a-5667-44ae-9739-897a4d19512d
-- title:
--   Theorem 5.1.
-- statement:
--   Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space, let $0<\alpha<1$, and define $A^\alpha=(z^\alpha)(A)$ with the principal complex branch. Then
--   $$\|C_t(A)x\|=O(t^{-\alpha})\quad\text{for every }x\in\operatorname{ran}A^\alpha.$$
--   If $T$ is mean ergodic, these estimates are little-o. If nonzero spectral points of $A$ accumulate at zero, every positive nonincreasing $\epsilon(t)\to0$ admits $y\in\operatorname{ran}A^\alpha$ with $\sup_{t\ge1}t^\alpha\|C_t(A)y\|/\epsilon(t)=+\infty$. All three parts concern actual ranges; injectivity is not imposed.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 21, Theorem 5.1.

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

/-- PDF pp.21–22, Theorem 5.1: principal fractional power (z^alpha)(A),
with all three parts and actual ranges. -/
theorem fractional_rates (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T)
    (alpha : ℝ) (ha : 0 < alpha) (hb : alpha < 1) :
    (∀ x ∈ graphRange (hpGraph T (fun z => z ^ (alpha : ℂ))),
      Asymptotics.IsBigO atTop (fun t => ‖continuousCesaro T t x‖) (fun t : ℝ => Real.rpow t (-alpha))) ∧
    (MeanErgodic T → ∀ x ∈ graphRange (hpGraph T (fun z => z ^ (alpha : ℂ))),
      Asymptotics.IsLittleO atTop (fun t => ‖continuousCesaro T t x‖) (fun t : ℝ => Real.rpow t (-alpha))) ∧
    (SpectralAccumulation T → ∀ e : ℝ → ℝ, VanishingFactor e →
      ∃ y ∈ graphRange (hpGraph T (fun z => z ^ (alpha : ℂ))), ∀ K : ℝ,
        ∃ t : ℝ, 1 ≤ t ∧ K < Real.rpow t alpha * ‖continuousCesaro T t y‖ / e t) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
