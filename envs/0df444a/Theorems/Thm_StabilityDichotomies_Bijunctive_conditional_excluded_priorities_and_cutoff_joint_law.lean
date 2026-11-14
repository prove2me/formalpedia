-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_excluded_priorities_and_cutoff_joint_law
-- name    : StabilityDichotomies.Bijunctive.conditional_excluded_priorities_and_cutoff_joint_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:28:57.056382+00:00
-- url     : https://prove2.me/theorems/c94a4caf-51b3-4fd8-a1e1-53363cb28313
-- title:
--   Excluded priorities and the cutoff are conditionally iid
-- statement:
--   Conditional on any first-stage occurrence mask, the priorities of excluded occurrences and the common cutoff are mutually independent and all have the same uniform law on $[1-\varepsilon/2,1]$. This is the joint random input required for the random-order comparison in Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, conditioning on the first-stage constraint set.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.conditional_excluded_priorities_and_cutoff_joint_law {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool) :
    Measure.map (fun z : (α → ℝ) × ℝ => (fun i : {i // m i = false} => z.1 i, z.2))
      (ProbabilityTheory.cond ((Measure.pi (fun _ : α => unitPriorityMeasure)).prod (cutoffMeasure ε))
        ((Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) ×ˢ Set.univ)) =
    (Measure.pi (fun _ : {i // m i = false} => cutoffMeasure ε)).prod (cutoffMeasure ε) := by
  sorry
