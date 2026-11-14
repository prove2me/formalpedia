-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_first_mask_priority_law
-- name    : StabilityDichotomies.Bijunctive.conditional_first_mask_priority_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:23:56.13106+00:00
-- url     : https://prove2.me/theorems/792d75f7-7834-4bd7-ab07-5bb55929c148
-- title:
--   The priority vector conditioned on its first-stage mask is an independent product
-- statement:
--   Fix an arbitrary pattern of first-stage included and excluded constraint occurrences. Condition the independent uniform priority vector on this pattern. The resulting priorities remain mutually independent; included coordinates have the corresponding lower-interval conditional law, while every excluded coordinate has the same uniform upper-interval law as the common cutoff. This is the conditional product-law step in the proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, conditioning on the first-stage constraint set.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.conditional_first_mask_priority_law {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool) :
    ProbabilityTheory.cond (Measure.pi (fun _ : α => unitPriorityMeasure))
      (Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) =
    Measure.pi (fun i => if m i then ProbabilityTheory.cond unitPriorityMeasure (Iic (1 - ε / 2))
      else cutoffMeasure ε) := by
  sorry
