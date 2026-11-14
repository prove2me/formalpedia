-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_shortest_distance_preserved_if_path_survives
-- name    : StabilityDichotomies.Bijunctive.shortest_distance_preserved_if_path_survives
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:04:44.653201+00:00
-- url     : https://prove2.me/theorems/d81359e1-4636-4e57-b777-fe509c41877f
-- title:
--   A surviving shortest path preserves its distance after arc deletion
-- statement:
--   If an implication graph loses arcs but retains a shortest walk of length $n$ from a root to a target, then their new shortest-path distance remains $n$.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph deletion step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.shortest_distance_preserved_if_path_survives {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (G G' : Instance Γ V)
    (hsub : ∀ a b, implicationArc rep G' a b → implicationArc rep G a b)
    (root target : Literal V) (n : ℕ)
    (hd : implicationDistance rep G root target = some n)
    (hw : WalkLength (implicationArc rep G') n root target) :
    implicationDistance rep G' root target = some n := by
  sorry
