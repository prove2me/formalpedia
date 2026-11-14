-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_excluded_cutoff_order_uniform
-- name    : StabilityDichotomies.Bijunctive.conditional_excluded_cutoff_order_uniform
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:34:08.246242+00:00
-- url     : https://prove2.me/theorems/68e5eb26-a5a7-48dd-9063-33e994210055
-- title:
--   Conditioned excluded priorities and cutoff have a uniform ordering
-- statement:
--   Fix an arbitrary first-stage occurrence mask with $k$ excluded occurrences. Conditional on this mask, every one of the $(k+1)!$ strict orderings of the excluded occurrence priorities and the common cutoff has probability $1/(k+1)!$. This is the precise joint uniform-order assertion used in the sensitivity proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, conditioning on the first-stage constraint set.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.conditional_excluded_cutoff_order_uniform {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool)
    (n : ℕ) (e : Fin n ≃ Option {i // m i = false}) (p : Equiv.Perm (Fin n)) :
    let f := (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm) ∘
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i // m i = false} => ℝ)).symm ∘
      (fun z : (α → ℝ) × ℝ => (fun i : {i // m i = false} => z.1 i, z.2))
    (ProbabilityTheory.cond ((Measure.pi (fun _ : α => unitPriorityMeasure)).prod (cutoffMeasure ε))
        ((Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) ×ˢ Set.univ)
      {z | ∀ i, (Finset.univ.filter (fun j : Fin n => f z j < f z i)).card = (p i).val}).toReal =
    1 / n.factorial := by
  sorry
