-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_retained_constraints_approximation
-- name    : StabilityDichotomies.Solvability.retained_constraints_approximation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:56:25.115199+00:00
-- url     : https://prove2.me/theorems/013b7628-6a8f-48a9-b182-2222a6cd6345
-- title:
--   Retained-constraint satisfaction gives an approximation bound
-- statement:
--   Consider a finite randomized experiment that outputs an assignment and a set of retained constraint types. Suppose every retained constraint is satisfied, and each constraint appearing in the instance fails to be retained with probability at most $\varepsilon$. Then the expected number of violated constraint occurrences is at most $\varepsilon$ times the total number of occurrences. Repeated constraints are counted with multiplicity. This is the probability-to-approximation step of the thinning construction in Theorem 4.3; it does not require independent retention.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.16.

import Definitions.Def_StabilityDichotomies_Approximability_Core
noncomputable section
open scoped Classical BigOperators

namespace StabilityDichotomies.Solvability
theorem retained_constraints_approximation
    {Γ : Language} {V : Type} [Fintype V] (I : Instance Γ V)
    (Ω : Type) [Fintype Ω] (μ : PMF Ω) (output : Ω → V → Bool)
    (retained : Ω → Constraint Γ V → Prop)
    (ε : ℝ)
    (hsatisfy : ∀ ω c, c ∈ I.constraints → retained ω c → c.Satisfied (output ω))
    (homit : ∀ c ∈ I.constraints,
      (∑ ω : Ω, (μ ω).toReal * (if ¬ retained ω c then (1 : ℝ) else 0)) ≤ ε) :
    (∑ ω : Ω, (μ ω).toReal * (violationCount I (output ω) : ℝ)) ≤
      ε * I.constraints.card := by sorry
end StabilityDichotomies.Solvability
