-- Prove2me | Theorems.Thm_ProbabilityTheory_finite_oracle_covariance_energy_le_entropy_drop
-- name    : ProbabilityTheory.finite_oracle_covariance_energy_le_entropy_drop
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T18:30:35.873878+00:00
-- url     : https://prove2.me/theorems/ae482d33-bcc7-49fc-b5de-bc4a7c5f87d1
-- title:
--   Entropy decrease controls diagonal oracle covariance energy in a bounded finite experiment
-- statement:
--   In a bounded finite experiment with posterior-matched action probabilities, the sum of squared expected diagonal oracle covariances is bounded by half the squared reward scale times posterior entropy decrease. Prove this through finite-label augmentation, conditional bounded-mean Pinsker, diagonal retention, Jensen, and entropy monotonicity. Zero scale and zero posterior masses require separate zero-term arguments. Ambient measurable-space arguments are explicit to repair the supplied diagnostic.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Definitions.Def_OnlineNRM_TSFixed_EntropyExperiment

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem ProbabilityTheory.finite_oracle_covariance_energy_le_entropy_drop
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [fα : Fintype α]
    [mα : MeasurableSpace α] [hα : MeasurableSingletonClass α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H L G : MeasurableSpace Ω) (w r : Ω → α → ℝ)
    (B : Ω → α) (Y : Ω → ℝ) (R : ℝ)
    (hexp : @IsFiniteOracleExperiment Ω α mΩ fα mα hα
      P H L G w r B Y R) :
    (∑ a : α, (@weightedOracleCovariance Ω α mΩ P H w r a) ^ 2) ≤
      R ^ 2 / 2 *
        (@finitePosteriorEntropy Ω α mΩ fα P H w -
          @finitePosteriorEntropy Ω α mΩ fα P G w) := by sorry
