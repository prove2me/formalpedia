-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_boolean_bounded_width_criterion
-- name    : StabilityDichotomies.Solvability.boolean_bounded_width_criterion
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T06:15:52.392986+00:00
-- url     : https://prove2.me/theorems/2a597783-229f-43c2-9d36-05243d237471
-- title:
--   Proposition 2.9: Boolean bounded-width criterion
-- statement:
--   A finite Boolean constraint language has bounded width if and only if it is 0-valid, 1-valid, Horn, dual-Horn, or bijunctive. The formal statement uses closure under coordinatewise AND, OR, and majority for Horn, dual-Horn, and bijunctive relations respectively; these are the standard equivalent Boolean polymorphism characterizations. The bounded-width side is the semantic local-strategy definition.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Proposition 2.9, p.10 (citing Barto and Kozik 2014).

import Definitions.Def_StabilityDichotomies_Approximability_Core
import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
noncomputable section
open scoped Classical

namespace StabilityDichotomies.Solvability
theorem boolean_bounded_width_criterion (Γ : Language) :
    BoundedWidth Γ ↔ Valid Γ false ∨ Valid Γ true ∨
      (∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
        x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples) ∨
      (∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
        x ∈ R.tuples → y ∈ R.tuples → (fun i => x i || y i) ∈ R.tuples) ∨
      (∀ R ∈ Γ.relations, ∀ x y z : Fin R.arity → Bool,
        x ∈ R.tuples → y ∈ R.tuples → z ∈ R.tuples →
        (fun i => (x i && y i) || (x i && z i) || (y i && z i)) ∈ R.tuples) := by sorry
end StabilityDichotomies.Solvability
