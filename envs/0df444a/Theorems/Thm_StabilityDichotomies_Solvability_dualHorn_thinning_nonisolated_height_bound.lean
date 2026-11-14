-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_dualHorn_thinning_nonisolated_height_bound
-- name    : StabilityDichotomies.Solvability.dualHorn_thinning_nonisolated_height_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:36:47.909202+00:00
-- url     : https://prove2.me/theorems/1ff36c95-6250-4518-aabd-db7027ec58a0
-- title:
--   Dual-Horn thinning output false coordinates are non-isolated
-- statement:
--   For a satisfiable dual-Horn instance, the greatest solution of every thinned subinstance is true at variables outside the original constraint support. Thus its number of false coordinates is at most the number of original non-isolated variables.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.dualHorn_thinning_nonisolated_height_bound (Γ : Language)
    (hDualHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i || y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (mask : Fin I.constraints.card → Bool) :
    (∑ v : V, if !(extremalSolution (thinnedInstance I mask) true v) then (1 : ℝ) else 0) ≤
      ((I.constraints.toFinset.biUnion fun c => Finset.univ.image c.scope).card : ℝ) := by sorry
