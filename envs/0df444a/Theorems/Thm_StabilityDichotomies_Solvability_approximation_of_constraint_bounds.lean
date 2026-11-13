-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_approximation_of_constraint_bounds
-- name    : StabilityDichotomies.Solvability.approximation_of_constraint_bounds
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:56:48.746973+00:00
-- url     : https://prove2.me/theorems/ba409759-a1ee-4768-b5b3-efe66371b262
-- title:
--   Per-constraint error bounds imply approximate satisfaction
-- statement:
--   Let $A$ be a randomized solver for a Boolean constraint language. Suppose that on every satisfiable finite instance and for each constraint occurring in it, $A$ violates that constraint with probability at most $\varepsilon$. Then $A$ violates at most an $\varepsilon$ fraction of the constraint occurrences in expectation. Repeated constraints are counted with their multiplicities.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.16.

import Definitions.Def_StabilityDichotomies_Approximability_Core
noncomputable section
open scoped Classical BigOperators

namespace StabilityDichotomies.Solvability
theorem approximation_of_constraint_bounds
    (Γ : Language) (A : Solver Γ) (ε : ℝ)
    (h : ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
      ∀ c ∈ I.constraints,
        (∑ x : V → Bool, (A V I x).toReal * (if ¬ c.Satisfied x then (1 : ℝ) else 0)) ≤ ε) :
    Approximates A ε := by sorry
end StabilityDichotomies.Solvability
