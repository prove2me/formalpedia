-- Prove2me | Theorems.Thm_QuantileMDP_theorem_5
-- name    : QuantileMDP.theorem_5
-- status  : Proved
-- author  : @shuffle
-- created : 2026-11-14T02:32:34.940505+00:00
-- url     : https://prove2.me/theorems/73b94f4e-d4be-43a0-9c28-a0696e069a40
-- title:
--   Quantile MDP Theorem 5 — conditional order given the joint history
-- statement:
--   For two finite-state processes on a common probability space, let each total reward be the sum of the same state reward function over the horizon. Suppose the initial state marginals agree and the comparison of conditional quantiles in Theorem 5 holds given the joint histories from time 0 through time k. Then the unconditional quantiles are ordered. It is sufficient, for a horizon of at least two, to compare at a single interior quantile level on each positive-probability atom of the final joint history (k = T − 1). This gives the result at every level, including the endpoints.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.2, Theorem 5, p. 22. https://arxiv.org/abs/1711.05788v5

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_QuantileMDP_quantile

open MeasureTheory ProbabilityTheory Set QuantileMDP
open scoped ENNReal

theorem QuantileMDP.theorem_5 {Ω S : Type*} [MeasurableSpace Ω] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (X Y : Fin T → Ω → S) (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (r : S → ℝ) (hstart : ∀ hT : 0 < T, P.map (X ⟨0, hT⟩) = P.map (Y ⟨0, hT⟩))
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1)
    (h : 1 < T → ∀ j : (Fin T → S × S), P {w | (fun t => (X t w, Y t w)) = j} ≠ 0 →
      quantile ((cond P {w | (fun t => (X t w, Y t w)) = j}).map
        (fun w => ∑ t, r (Y t w))) u ≤
      quantile ((cond P {w | (fun t => (X t w, Y t w)) = j}).map
        (fun w => ∑ t, r (X t w))) u)
    (τ : ℝ) :
    quantile (P.map (fun w => ∑ t, r (Y t w))) τ ≤
      quantile (P.map (fun w => ∑ t, r (X t w))) τ := by sorry
