-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_excluded_cutoff_iid_fin_law
-- name    : StabilityDichotomies.Bijunctive.conditional_excluded_cutoff_iid_fin_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:32:07.095217+00:00
-- url     : https://prove2.me/theorems/c6bcdf0f-bf10-4f7e-bd85-00614083aa33
-- title:
--   Conditional cutoff and excluded priorities form a finite iid sample
-- statement:
--   Conditional on any first-stage mask, reindex the excluded priority values together with the cutoff as a finite sequence. The resulting sequence has the finite product of the common upper-interval uniform distribution. Combined with uniform ordering of an iid continuous sample, this supplies the source random-order law.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, conditioning on the first-stage constraint set.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.conditional_excluded_cutoff_iid_fin_law {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool)
    (n : ℕ) (e : Fin n ≃ Option {i // m i = false}) :
    Measure.map ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm) ∘
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i // m i = false} => ℝ)).symm ∘
      (fun z : (α → ℝ) × ℝ => (fun i : {i // m i = false} => z.1 i, z.2)))
      (ProbabilityTheory.cond ((Measure.pi (fun _ : α => unitPriorityMeasure)).prod (cutoffMeasure ε))
        ((Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) ×ˢ Set.univ)) =
    Measure.pi (fun _ : Fin n => cutoffMeasure ε) := by
  sorry
