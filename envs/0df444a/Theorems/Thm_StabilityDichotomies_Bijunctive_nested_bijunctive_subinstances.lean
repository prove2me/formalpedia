-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_nested_bijunctive_subinstances
-- name    : StabilityDichotomies.Bijunctive.nested_bijunctive_subinstances
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:49:33.429785+00:00
-- url     : https://prove2.me/theorems/da51caae-84d1-454f-83ba-750e1698e387
-- title:
--   The two priority-thinned instances are nested and satisfiable
-- statement:
--   For a satisfiable input, a priority threshold at most the feasibility cutoff produces a satisfiable feasibility subinstance containing the graph subinstance. Any original constraint occurrence whose priority is below the graph threshold is retained in that graph subinstance.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Definition 4.8 and proof of Theorem 4.9.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.nested_bijunctive_subinstances {Γ : Language} {V : Type}
    (I : Instance Γ V) (hI : Satisfiable I) (ε cutoff : ℝ)
    (priority : Fin I.constraints.card → ℝ) (hcut : 1 - ε / 2 ≤ cutoff) :
    let G := thinnedInstance I (fun i => decide (priority i ≤ 1 - ε / 2))
    let F := thinnedInstance I (fun i => decide (priority i ≤ cutoff))
    Satisfiable F ∧ (∀ c ∈ G.constraints, c ∈ F.constraints) ∧
      ∀ i, priority i ≤ 1 - ε / 2 → occurrenceAt I i ∈ G.constraints := by
  sorry
