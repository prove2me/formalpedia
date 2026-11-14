-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_cutoff_order_partition_ae
-- name    : StabilityDichotomies.Bijunctive.conditional_cutoff_order_partition_ae
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T11:16:30.915477+00:00
-- url     : https://prove2.me/theorems/16e3d0ad-c55b-455b-b232-28ddca442d40
-- title:
--   Conditional cutoff and excluded-priority order cells partition almost surely
-- statement:
--   Conditional on any first-stage mask, the cutoff and all excluded priorities have a unique strict ordering almost surely. Equivalently, the corresponding permutation-order cells form an almost-sure partition of the conditioned priority/cutoff space.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, conditional uniform order.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.conditional_cutoff_order_partition_ae {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool)
    (n : ℕ) (e : Fin n ≃ Option {i // m i = false}) :
    let f := (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm) ∘
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i // m i = false} => ℝ)).symm ∘
      (fun z : (α → ℝ) × ℝ => (fun i : {i // m i = false} => z.1 i, z.2))
    ∀ᵐ z ∂(ProbabilityTheory.cond ((Measure.pi (fun _ : α => unitPriorityMeasure)).prod (cutoffMeasure ε))
        ((Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) ×ˢ Set.univ)),
      ∃! p : Equiv.Perm (Fin n), ∀ i, (Finset.univ.filter (fun j : Fin n => f z j < f z i)).card = (p i).val := by
  sorry
