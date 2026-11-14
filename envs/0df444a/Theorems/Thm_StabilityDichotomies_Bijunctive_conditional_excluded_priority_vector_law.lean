-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_excluded_priority_vector_law
-- name    : StabilityDichotomies.Bijunctive.conditional_excluded_priority_vector_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:27:08.290708+00:00
-- url     : https://prove2.me/theorems/0004dd78-0af1-4ddc-8f9f-6679e34388b9
-- title:
--   Excluded priorities are conditionally iid with the cutoff law
-- statement:
--   Fix an arbitrary first-stage mask. Conditional on that mask, the priority values of all excluded occurrences form an independent sample from the same uniform interval distribution as the cutoff. This is the exact marginal law used to order the excluded constraints in the proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, conditioning on the first-stage constraint set.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.conditional_excluded_priority_vector_law {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool) :
    Measure.map (fun x : α → ℝ => fun i : {i // m i = false} => x i)
      (ProbabilityTheory.cond (Measure.pi (fun _ : α => unitPriorityMeasure))
        (Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)))) =
    Measure.pi (fun _ : {i // m i = false} => cutoffMeasure ε) := by
  sorry
