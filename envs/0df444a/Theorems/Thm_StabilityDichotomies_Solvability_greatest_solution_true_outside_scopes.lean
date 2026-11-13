-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_greatest_solution_true_outside_scopes
-- name    : StabilityDichotomies.Solvability.greatest_solution_true_outside_scopes
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:05:01.887227+00:00
-- url     : https://prove2.me/theorems/93586e65-99f7-487c-9608-d7da7ccf518f
-- title:
--   Greatest solutions are true at isolated variables
-- statement:
--   Any variable absent from every constraint of an instance is assigned true by a coordinatewise greatest satisfying assignment. This supplies the fixed-coordinate condition in the monotone-thinning analysis.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.17.

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical BigOperators

namespace StabilityDichotomies.Solvability
theorem greatest_solution_true_outside_scopes {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) (xmax : V → Bool) (hmax : Solution I xmax)
    (hgreatest : ∀ x, Solution I x → x ≤ xmax)
    (v : V) (hv : ∀ c ∈ I.constraints, ∀ i, c.scope i ≠ v) : xmax v = true := by sorry
end StabilityDichotomies.Solvability
