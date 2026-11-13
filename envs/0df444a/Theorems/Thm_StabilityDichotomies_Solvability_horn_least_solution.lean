-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_horn_least_solution
-- name    : StabilityDichotomies.Solvability.horn_least_solution
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:47:55.557198+00:00
-- url     : https://prove2.me/theorems/78d31a0d-5b47-4c77-9f0a-51ce108faf1b
-- title:
--   Horn instances have a least satisfying assignment
-- statement:
--   Let $\Gamma$ be a finite Boolean constraint language whose relations are closed under coordinatewise AND. Every satisfiable finite instance over $\Gamma$ has a coordinatewise least satisfying assignment: it satisfies the instance and is at most every other satisfying assignment in the Boolean order. This is the Horn structural fact used in the proof of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Section 4.1, p.16, proof of Theorem 4.3 (citing Horn 1951).

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical

namespace StabilityDichotomies.Solvability
theorem horn_least_solution
    (Γ : Language)
    (hHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I) :
    ∃ xmin : V → Bool, Solution I xmin ∧ ∀ x : V → Bool, Solution I x → xmin ≤ x := by sorry
end StabilityDichotomies.Solvability
