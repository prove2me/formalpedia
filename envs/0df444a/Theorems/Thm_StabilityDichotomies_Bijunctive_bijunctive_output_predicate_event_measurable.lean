-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_predicate_event_measurable
-- name    : StabilityDichotomies.Bijunctive.bijunctive_output_predicate_event_measurable
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:50:19.112735+00:00
-- url     : https://prove2.me/theorems/801333a8-d16b-48e0-8589-6ff48a1324cc
-- title:
--   Every predicate of the bijunctive output is measurable
-- statement:
--   For a finite variable set, the event that the bijunctive algorithm output satisfies any specified property is measurable in the product seed space. In particular, events that a fixed output clause or constraint is violated are measurable.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Definition 4.8 and proof of Theorem 4.9.

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
open scoped Classical BigOperators
open MeasureTheory Set StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_output_predicate_event_measurable {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (P : (V → Bool) → Prop) :
    MeasurableSet {s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
      P (bijunctiveOutput rep I ε s.1 s.2.1 s.2.2)} := by
  sorry
