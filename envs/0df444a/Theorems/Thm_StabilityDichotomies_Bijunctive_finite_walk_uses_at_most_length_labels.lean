-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_finite_walk_uses_at_most_length_labels
-- name    : StabilityDichotomies.Bijunctive.finite_walk_uses_at_most_length_labels
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:06:00.063278+00:00
-- url     : https://prove2.me/theorems/aaa1031f-0f6d-4400-b32e-99cd4859804d
-- title:
--   A finite walk uses at most its length many arc labels
-- statement:
--   If each directed arc in a walk carries at least one label, a walk of length $n$ admits a choice of at most $n$ labels covering all of its arcs. The labels can represent constraint occurrences whose deletions can destroy that walk.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-deletion sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.finite_walk_uses_at_most_length_labels {α ι : Type} (arc : ι → α → α → Prop)
    (n : ℕ) (a b : α) (hw : WalkLength (fun x y => ∃ i, arc i x y) n a b) :
    ∃ S : Finset ι, S.card ≤ n ∧
      WalkLength (fun x y => ∃ i ∈ S, arc i x y) n a b := by
  sorry
