-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_fact_18
-- name    : SYKFastMix.FastMixing.fact_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:11.44566+00:00
-- url     : https://prove2.me/theorems/ddfdf0a7-33c5-465d-915d-13ac1f1a89e0
-- title:
--   Fact 18 — sharp compact-index Borell–TIS including zero threshold
-- statement:
--   Let $(X_t)_{t\in T}$ be a centered real Gaussian process on a probability space $(\Omega,P)$, with almost-sure continuous sample paths on a nonempty compact metric space $T$. Set $v^2=\sup_t\mathbb E_P X_t^2>0$. Then the coordinate variances are bounded, the sample supremum is almost surely bounded, and its expectation is finite. For every real $u\ge0$,
--   $$P\left[\sup_tX_t>\mathbb E_P\sup_tX_t+u\right]\le\exp\left(-\frac{u^2}{2v^2}\right).$$
--   The sharp denominator $2v^2$, the strict event, and $u=0$ are retained. This supplies the continuous-index concentration needed for the quartic Gaussian field.
--
--   Differences from the source:
--   - encoding: continuous compact-index supremum and its finite expectation → nonempty compact metric index, almost-sure sample boundedness, bounded variances, and Integrable supremum; reason: the extra conclusion bookkeeping ensures the real supremum and integral have their mathematical meanings; continuity is interpreted almost surely
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 33, Fact 18, Eq. (A.5)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem fact_18 {T Ω : Type} [MetricSpace T] [CompactSpace T] [Nonempty T]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) (hX : CompactGaussian P X) (hv : 0 < varianceSup P X) :
  BddAbove (Set.range (fun t => ∫ ω, (X t ω)^2 ∂P)) ∧
  (∀ᵐ ω ∂P, BddAbove (Set.range (fun t => X t ω))) ∧
  Integrable (sampleSup X) P ∧
  ∀ u : ℝ, 0 ≤ u →
    P {ω | sampleSup X ω > (∫ v, sampleSup X v ∂P) + u} ≤
      ENNReal.ofReal (Real.exp (-(u^2) / (2 * varianceSup P X))) := by sorry

end SYKFastMix.FastMixing
