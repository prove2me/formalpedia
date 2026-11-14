-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_first_mask_single_flip_probability_balance
-- name    : StabilityDichotomies.Bijunctive.first_mask_single_flip_probability_balance
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:35:41.522208+00:00
-- url     : https://prove2.me/theorems/8e19b943-9c13-4a9b-af25-79dc785ea1d0
-- title:
--   First-stage mask probabilities satisfy the single-occurrence balance identity
-- statement:
--   Fix all first-stage inclusion decisions except one occurrence. Let $P_1$ and $P_0$ be the probabilities that the occurrence is respectively included and excluded while all the other decisions stay fixed. Then
--   $$\frac{\varepsilon}{2}P_1=\left(1-\frac{\varepsilon}{2}\right)P_0.$$
--   For positive $\varepsilon$, this is the source change-of-measure ratio $(2-\varepsilon)/\varepsilon$ in the inside-first-stage deletion argument.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, inside-first-stage deletion averaging.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.first_mask_single_flip_probability_balance {α : Type} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (m : α → Bool) (c : α) :
    (ε / 2) * (Measure.pi (fun _ : α => unitPriorityMeasure)
      (Set.univ.pi (fun i => if Function.update m c true i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)))).toReal =
    (1 - ε / 2) * (Measure.pi (fun _ : α => unitPriorityMeasure)
      (Set.univ.pi (fun i => if Function.update m c false i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)))).toReal := by
  sorry
