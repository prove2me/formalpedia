-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_fact_17_adapter
-- name    : SYKFastMix.FastMixing.fact_17_adapter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:10.664687+00:00
-- url     : https://prove2.me/theorems/283b9df1-92f1-46b0-8d9a-9606836574ca
-- title:
--   Fact 17 — compact continuous expected-supremum adapter
-- statement:
--   Let $T$ be a nonempty compact metric space, and let $X$ and $Y$ be centered real Gaussian processes with almost-sure continuous sample paths. The processes may be given on probability spaces $(\Omega,P)$ and $(\Omega',Q)$. Assume
--   $$\mathbb E_P(X_t-X_u)^2\le\mathbb E_Q(Y_t-Y_u)^2\qquad(t,u\in T).$$
--   Both pointwise suprema are almost surely bounded and integrable. Their expectations equal the corresponding published finite-marginal expected suprema, and
--   $$\mathbb E_P\sup_{t\in T}X_t\le\mathbb E_Q\sup_{t\in T}Y_t.$$
--   This is the compact-continuous adapter to the referenced Sudakov–Fernique comparison, including the identification and integrability obligations needed for its application to the sphere. It does not assume those obligations as extra process hypotheses.
--
--   Differences from the source:
--   - generalization: two Gaussian processes on a common probability space → the processes may have distinct probability spaces; reason: product coupling recovers the referenced comparison and specializes to the source by taking the same space
--   - encoding: expectations of pointwise compact sample suprema → integrability, almost-sure boundedness, and equality with processESup are explicit conclusions; reason: this bridges the two supremum conventions without replacing the compact index by a finite grid
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 33, Fact 17, Eq. (A.4)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem fact_17_adapter {T Ω Ω' : Type} [MetricSpace T] [CompactSpace T] [Nonempty T]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : T → Ω → ℝ) (Y : T → Ω' → ℝ)
    (hX : CompactGaussian P X) (hY : CompactGaussian Q Y)
    (hinc : ∀ t u, ∫ ω, (X t ω - X u ω)^2 ∂P ≤ ∫ ω, (Y t ω - Y u ω)^2 ∂Q) :
  (∀ᵐ ω ∂P, BddAbove (Set.range (fun t => X t ω))) ∧
  (∀ᵐ ω ∂Q, BddAbove (Set.range (fun t => Y t ω))) ∧
  Integrable (sampleSup X) P ∧ Integrable (sampleSup Y) Q ∧
  HighDimProb.RandomProcesses.processESup P X = ((∫ ω, sampleSup X ω ∂P : ℝ) : EReal) ∧
  HighDimProb.RandomProcesses.processESup Q Y = ((∫ ω, sampleSup Y ω ∂Q : ℝ) : EReal) ∧
  (∫ ω, sampleSup X ω ∂P) ≤ ∫ ω, sampleSup Y ω ∂Q := by sorry

end SYKFastMix.FastMixing
