-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_horn_thinning_nonisolated_height_bound
-- name    : StabilityDichotomies.Solvability.horn_thinning_nonisolated_height_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:31:27.557093+00:00
-- url     : https://prove2.me/theorems/38cf910d-af89-4e5a-92d5-0ec5d7ac00a1
-- title:
--   Horn thinning output height is bounded by non-isolated variables
-- statement:
--   For a satisfiable Horn instance, the least solution of every thinned subinstance is false outside the variables appearing in the original constraints. Consequently its number of ones is at most the number of original non-isolated variables.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.horn_thinning_nonisolated_height_bound (Γ : Language)
    (hHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (mask : Fin I.constraints.card → Bool) :
    (∑ v : V, if extremalSolution (thinnedInstance I mask) false v then (1 : ℝ) else 0) ≤
      ((I.constraints.toFinset.biUnion fun c => Finset.univ.image c.scope).card : ℝ) := by sorry
