-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_first_mask_inside_deletion_cost_regroup
-- name    : StabilityDichotomies.Bijunctive.first_mask_inside_deletion_cost_regroup
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:38:34.658044+00:00
-- url     : https://prove2.me/theorems/608675d5-9ae7-4d71-9b46-aac60b52ea00
-- title:
--   Inside-mask deletion costs regroup by the remaining first-stage mask
-- statement:
--   Assign an arbitrary real cost to each remaining first-stage mask and deleted occurrence. Average the costs of deletions inside the first-stage mask using their exact independent-priority probabilities. Regrouping each mask by deleting the chosen occurrence produces the corresponding average over masks excluding that occurrence, with the exact factor $(2-\varepsilon)/\varepsilon$ for positive $\varepsilon$. The formal identity is cross-multiplied, so it also holds at $\varepsilon=0$.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, inside-first-stage deletion averaging.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.first_mask_inside_deletion_cost_regroup {α : Type} [Fintype α] [DecidableEq α]
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (cost : (α → Bool) → α → ℝ) :
    let P : (α → Bool) → ℝ := fun m => (Measure.pi (fun _ : α => unitPriorityMeasure)
      (Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2)))).toReal
    (ε / 2) * (∑ c : α, ∑ m : α → Bool, if m c then P m * cost (Function.update m c false) c else 0) =
    (1 - ε / 2) * (∑ c : α, ∑ m : α → Bool, if m c then 0 else P m * cost m c) := by
  sorry
