-- Prove2me | Theorems.Thm_WaitJudge_Generic_prob_violation_eq_sum_integral
-- name    : WaitJudge.Generic.prob_violation_eq_sum_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:11:06.589629+00:00
-- url     : https://prove2.me/theorems/af0a77df-37d6-4fbe-814b-75aed99eda29
-- title:
--   Sect. 7.1, p. 24 — violation probability as an F_k integral sum
-- statement:
--   For a generic scenario program satisfying Assumptions 1–2 and the stated measurability convention, let N≥1 and let ε(k) lie in [0,1] for 0≤k≤N. Then the chance that the N-sample solution violates a new constraint with probability greater than ε(s*_N) is
--
--   $$
--   \mathbb P^N\{V(x^*_N)>\varepsilon(s^*_N)\}
--   =\sum_{k=0}^{N}{N\choose k}\int_{(\varepsilon(k),1]}(1-v)^{N-k}\,dF_k(v).
--   $$
--
--   This identity expresses the tail event using the generalized distribution functions F_k, which are the inputs to the moment problem.
--
--   **Formalization Note** The integral is a Lebesgue integral against the finite measure F_k, and the probability on the left is converted from an extended nonnegative real to a real. The interval is open at ε(k) and closed at 1. Samples use zero-based indices; the hypotheses include the paper's Assumptions 1–2 and footnote-1 measurability pins.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF p. 24, Sect. 7.1, decomposition following (13) and (17)

import Mathlib
import Definitions.Def_WaitJudge_Generic_Setting

namespace WaitJudge.Generic

open MeasureTheory

theorem prob_violation_eq_sum_integral
    {S Δ : Type*} [Nonempty S] [MeasurableSpace S] [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S)
    {p : ℕ} (tb : Fin p → S → ℝ)
    (hA1 : Assumption1 f X Xδ tb)
    (hA2 : Assumption2 f X Xδ tb P)
    (hmeas : MeasurabilityPins f X Xδ tb)
    (N : ℕ) (hN : 0 < N) (ε : ℕ → ℝ)
    (hε : ∀ k ≤ N, 0 ≤ ε k ∧ ε k ≤ 1) :
    ((Measure.pi fun _ : Fin N => P)
      {ω : Fin N → Δ | ε (sstar f X Xδ tb ω) <
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω)}).toReal =
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
      ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(Fk f X Xδ tb P k) := by sorry

end WaitJudge.Generic
