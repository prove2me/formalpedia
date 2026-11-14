-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_deleted_seed_is_shared_priority_marginal
-- name    : StabilityDichotomies.Bijunctive.bijunctive_deleted_seed_is_shared_priority_marginal
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:43:17.978079+00:00
-- url     : https://prove2.me/theorems/7c1f801f-2f46-479c-a712-30006523a2dc
-- title:
--   The deleted-instance seed is a marginal of the original common seed
-- statement:
--   Discard the priority of one constraint occurrence from a Definition 4.8 random seed, reindex the remaining priorities, and retain the common cutoff and all exponential shifts. The resulting random seed has exactly the Definition 4.8 seed law of the instance with that occurrence deleted.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, common-randomness deletion coupling.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_deleted_seed_is_shared_priority_marginal {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (c : Constraint Γ V)
    (ε : ℝ) (hε : 0 < ε)
    (e : Fin I.constraints.card ≃ Option (Fin (I.delete c).constraints.card)) :
    Measure.map (fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      (fun i : Fin (I.delete c).constraints.card => z.1 (e.symm (some i)), z.2))
      (bijunctiveSeedMeasure rep I ε) = bijunctiveSeedMeasure rep (I.delete c) ε := by
  sorry
