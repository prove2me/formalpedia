-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_delete_occurrence_equivalence
-- name    : StabilityDichotomies.Solvability.delete_occurrence_equivalence
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:21:05.37897+00:00
-- url     : https://prove2.me/theorems/f0987c24-8f13-4586-9f55-8759c069ed3e
-- title:
--   Value-preserving occurrence equivalence after deleting one constraint
-- statement:
--   Let I be a constraint multiset and c an occurrence value belonging to it. The original occurrence indices are in value-preserving bijection with an optional index of I.delete c: the distinguished none index has value c, and each other index has the value of its matching occurrence in the erased multiset. Repeated equal constraints remain distinct. This bridges the independent occurrence orderings used in the deletion coupling.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, deletion coupling in proof of Theorem 4.3, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.delete_occurrence_equivalence {Γ : Language} {V : Type} (I : Instance Γ V)
    (c : Constraint Γ V) (hc : c ∈ I.constraints) :
    ∃ e : Fin I.constraints.card ≃ Option (Fin (I.delete c).constraints.card),
      ∀ j, (e j).elim c (occurrenceAt (I.delete c)) = occurrenceAt I j := by sorry
