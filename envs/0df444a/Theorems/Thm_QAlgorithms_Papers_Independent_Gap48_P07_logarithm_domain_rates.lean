-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_logarithm_domain_rates
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.logarithm_domain_rates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:25:28.744035+00:00
-- url     : https://prove2.me/theorems/90c8d67d-cb95-4f58-a524-bb0aa01ffc08
-- title:
--   Theorem 5.4.
-- statement:
--   Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space and suppose $A$ is injective. Define $\log A$ by the same-semigroup regularized Hille–Phillips calculus with principal logarithm. Then
--   $$\|C_t(A)x\|=O(1/\log t)\quad\text{for every }x\in\operatorname{dom}\log A.$$
--   If $\operatorname{ran}A$ is dense, the estimates are little-o. If nonzero spectral points of $A$ accumulate at zero, every positive nonincreasing $\epsilon(t)\to0$ admits $y\in\operatorname{dom}\log A$ with $\sup_{t\ge1}(\log t)\|C_t(A)y\|/\epsilon(t)=+\infty$. The asymptotic comparisons are eventually above one. This is the final domain-rate theorem, with its three distinct hypotheses kept in their respective clauses.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 24, Theorem 5.4.

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

/-- PDF pp.24–25, Theorem 5.4: logarithm graph domain; injectivity globally,
density only in (b), accumulation only in (c). -/
theorem logarithm_domain_rates (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T)
    (hinj : InjectiveGraph (negativeGenerator T)) :
    (∀ x ∈ graphDomain (hpGraph T Complex.log),
      Asymptotics.IsBigO atTop (fun t => ‖continuousCesaro T t x‖) (fun t : ℝ => 1 / Real.log t)) ∧
    (Dense (graphRange (negativeGenerator T)) → ∀ x ∈ graphDomain (hpGraph T Complex.log),
      Asymptotics.IsLittleO atTop (fun t => ‖continuousCesaro T t x‖) (fun t : ℝ => 1 / Real.log t)) ∧
    (SpectralAccumulation T → ∀ e : ℝ → ℝ, VanishingFactor e →
      ∃ y ∈ graphDomain (hpGraph T Complex.log), ∀ K : ℝ,
        ∃ t : ℝ, 1 ≤ t ∧ K < Real.log t * ‖continuousCesaro T t y‖ / e t) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
