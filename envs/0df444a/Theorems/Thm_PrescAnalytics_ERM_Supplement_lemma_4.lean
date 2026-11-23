-- Prove2me | Theorems.Thm_PrescAnalytics_ERM_Supplement_lemma_4
-- name    : PrescAnalytics.ERM.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:01:29.340645+00:00
-- url     : https://prove2.me/theorems/1eb528df-a256-4ba1-bd39-65ffbce5db28
-- title:
--   Lemma 4 (used in the proof of Theorem 16) — stationarity and all three mixing coefficients
-- statement:
--   Let $(X_i,Y_i)$ be a stationary sequence of Euclidean-valued random variables on a probability space, and let $f$ be a measurable real-valued function of the response. The transformed process $(X_i,f(Y_i))$ is stationary and, at every lag $k$,
--   $$\alpha_{(X,f(Y))}(k)\le\alpha_{(X,Y)}(k),\quad \beta_{(X,f(Y))}(k)\le\beta_{(X,Y)}(k),\quad \rho_{(X,f(Y))}(k)\le\rho_{(X,Y)}(k).$$
--   This transports the original data's dependence bounds to transformed costs and event indicators used by the kernel and recursive arguments.
--
--   Differences from the source:
--   - encoding: Stationary sequences start at observation 1. → Sequences start at 0; all lags, including lag 0, are covered.; reason: The past and future sigma algebras are unchanged after reindexing; measurability makes every pushforward an actual law.
--   - reading: The beta coefficient uses the printed TV notation. → TV is sup over measurable events, consistently on both sides.; reason: This fixes the convention without changing the data-processing inequality; alpha and rho use the published matching definitions.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 44, Lemma 4

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Supplement_Mixing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- Lemma 4, p. 44: stationarity and all three coefficients, for every lag. -/
theorem lemma_4
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {dx dy : ℕ}
    (S : ℕ → Ω → EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))
    (hS : ∀ i, Measurable (S i))
    (hstationary : MarkovChainCLT.IsStrictlyStationary P S)
    (f : EuclideanSpace ℝ (Fin dy) → ℝ) (hf : Measurable f) :
    MarkovChainCLT.IsStrictlyStationary P (fun i ω => ((S i ω).1, f (S i ω).2)) ∧
      ∀ k : ℕ,
        MarkovChainCLT.alphaMixingCoef P (fun i ω => ((S i ω).1, f (S i ω).2)) k ≤
          MarkovChainCLT.alphaMixingCoef P S k ∧
        betaMixingCoef P (fun i ω => ((S i ω).1, f (S i ω).2)) k ≤ betaMixingCoef P S k ∧
        MarkovChainCLT.rhoMixingCoef P (fun i ω => ((S i ω).1, f (S i ω).2)) k ≤
          MarkovChainCLT.rhoMixingCoef P S k := by sorry

end PrescAnalytics.ERM.Supplement
