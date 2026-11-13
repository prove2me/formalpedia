-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_retained_constraints_pushforward_approximation
-- name    : StabilityDichotomies.Solvability.retained_constraints_pushforward_approximation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:08:09.958198+00:00
-- url     : https://prove2.me/theorems/dd8e5b36-d31e-4c3e-9404-9bfd86a5568f
-- title:
--   Retention gives an approximation guarantee for the output law
-- statement:
--   Let a finite randomized experiment produce both a set of retained constraints and an assignment. Assume that its assignment satisfies every retained constraint, and that each constraint in the input is omitted with probability at most $\varepsilon$. Then the expected number of violated constraint occurrences under the output assignment law is at most $\varepsilon$ times the total number of occurrences. This is the approximation half of the thinning argument in Theorem 4.3, expressed using the pushforward output law.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.16.

import Definitions.Def_StabilityDichotomies_Approximability_Core
noncomputable section
open scoped Classical BigOperators ENNReal

namespace StabilityDichotomies.Solvability
theorem retained_constraints_pushforward_approximation
    {Γ : Language} {V : Type} [Fintype V] (I : Instance Γ V)
    (Ω : Type) [Fintype Ω] (μ : PMF Ω) (output : Ω → V → Bool)
    (retained : Ω → Constraint Γ V → Prop) (ε : ℝ)
    (hsatisfy : ∀ ω c, c ∈ I.constraints → retained ω c → c.Satisfied (output ω))
    (homit : ∀ c ∈ I.constraints,
      (∑ ω : Ω, (μ ω).toReal * (if ¬ retained ω c then (1 : ℝ) else 0)) ≤ ε) :
    (∑ x : V → Bool, ((μ.map output) x).toReal * (violationCount I x : ℝ)) ≤
      ε * I.constraints.card := by sorry
end StabilityDichotomies.Solvability
