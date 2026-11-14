-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_thinned_extremal_solution
-- name    : StabilityDichotomies.Solvability.thinned_extremal_solution
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:36:54.167715+00:00
-- url     : https://prove2.me/theorems/4d72cfea-4d22-4acf-9446-c5b93cb33301
-- title:
--   Extremal output satisfies every retained constraint
-- statement:
--   Let Γ be a Horn or dual-Horn Boolean language and let I be a satisfiable instance. For any selection of its constraint occurrences, the least solution in the Horn case, respectively greatest solution in the dual-Horn case, satisfies every selected constraint. The selection retains the original variable set, and repeated constraints are separate occurrences. This is the deterministic feasibility step in the approximation guarantee of the thinning algorithm.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.thinned_extremal_solution (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (mask : Fin I.constraints.card → Bool) :
    Solution (thinnedInstance I mask) (extremalSolution (thinnedInstance I mask) b) := by sorry
