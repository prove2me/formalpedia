-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_delete_equivalence_at_original_index
-- name    : StabilityDichotomies.Solvability.delete_equivalence_at_original_index
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:28:09.852319+00:00
-- url     : https://prove2.me/theorems/8ea5d09d-92c1-4291-90a5-91249fb833a6
-- title:
--   Occurrence alignment with any specified deleted index
-- statement:
--   For any original constraint occurrence index j, there is a value-preserving equivalence from the original indices to an optional index of the multiset after erasing the value at j, sending j to the distinguished absent coordinate. This is valid even when other occurrences have the same constraint value, and allows every occurrence to be charged to its own coordinate.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, deletion coupling in proof of Theorem 4.3, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.delete_equivalence_at_original_index {Γ : Language} {V : Type} (I : Instance Γ V)
    (j : Fin I.constraints.card) :
    ∃ e : Fin I.constraints.card ≃ Option (Fin (I.delete (occurrenceAt I j)).constraints.card),
      e j = none ∧
      ∀ k, (e k).elim (occurrenceAt I j) (occurrenceAt (I.delete (occurrenceAt I j))) = occurrenceAt I k := by sorry
