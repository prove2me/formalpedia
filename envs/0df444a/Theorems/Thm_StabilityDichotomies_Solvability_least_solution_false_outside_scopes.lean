-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_least_solution_false_outside_scopes
-- name    : StabilityDichotomies.Solvability.least_solution_false_outside_scopes
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:04:51.77379+00:00
-- url     : https://prove2.me/theorems/ca253495-9915-49fa-8d73-d3b3ab5c8306
-- title:
--   Least solutions vanish at isolated variables
-- statement:
--   Any variable absent from every constraint of an instance is assigned false by a coordinatewise least satisfying assignment. This supplies the fixed-coordinate condition in the monotone-thinning analysis.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.17.

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical BigOperators

namespace StabilityDichotomies.Solvability
theorem least_solution_false_outside_scopes {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) (xmin : V → Bool) (hmin : Solution I xmin)
    (hleast : ∀ x, Solution I x → xmin ≤ x)
    (v : V) (hv : ∀ c ∈ I.constraints, ∀ i, c.scope i ≠ v) : xmin v = false := by sorry
end StabilityDichotomies.Solvability
