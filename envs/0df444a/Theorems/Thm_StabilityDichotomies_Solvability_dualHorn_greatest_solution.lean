-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_dualHorn_greatest_solution
-- name    : StabilityDichotomies.Solvability.dualHorn_greatest_solution
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:47:53.379344+00:00
-- url     : https://prove2.me/theorems/08cbcdf6-cb6a-4684-b6e9-0d4eb7b9b41d
-- title:
--   Dual-Horn instances have a greatest satisfying assignment
-- statement:
--   Let $\Gamma$ be a finite Boolean constraint language whose relations are closed under coordinatewise OR. Every satisfiable finite instance over $\Gamma$ has a coordinatewise greatest satisfying assignment: it satisfies the instance and is at least every other satisfying assignment in the Boolean order. This is the dual-Horn structural fact used in the proof of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Section 4.1, p.16, proof of Theorem 4.3 (citing Horn 1951).

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical

namespace StabilityDichotomies.Solvability
theorem dualHorn_greatest_solution
    (Γ : Language)
    (hDualHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i || y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I) :
    ∃ xmax : V → Bool, Solution I xmax ∧ ∀ x : V → Bool, Solution I x → x ≤ xmax := by sorry
end StabilityDichotomies.Solvability
