-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_stable_approximability_dichotomy
-- name    : StabilityDichotomies.Solvability.stable_approximability_dichotomy
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T04:43:50.70055+00:00
-- url     : https://prove2.me/theorems/761d264a-6173-4125-ac1f-b7645574bf18
-- title:
--   Bounded width characterizes stable approximability
-- statement:
--   Let $\Gamma$ be a finite nonempty Boolean constraint language of nonempty positive-arity relations. Exactly one of the following holds.
--
--   1. $\Gamma$ has bounded width. For every $\varepsilon\in(0,1]$ there is a randomized $(1-\varepsilon)$-approximation algorithm whose average sensitivity on every satisfiable $n$-variable instance with $n\ge2$ is at most $C_\Gamma\varepsilon^{-1}\log n$.
--   2. $\Gamma$ does not have bounded width. There exist $\varepsilon_\Gamma\in(0,1]$, $c_\Gamma>0$, and an unbounded set $N_\Gamma$ of nonnegative integers such that every randomized $(1-\varepsilon_\Gamma)$-approximation algorithm has, for each $n\in N_\Gamma$, a satisfiable $n$-variable instance of average sensitivity at least $c_\Gamma n$.
--
--   Approximation is in expected number of violated constraint occurrences, algorithms are allowed unbounded computation, and sensitivity is average Wasserstein distance under deletion of one occurrence. The constants and unbounded size set in the lower branch are fixed by the language before choosing the algorithm. This is the paper's stable approximability dichotomy, distinct from its exact-solvability theorem.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Theorem 4.1, printed pp. 15–16 (Theorem 1.2 is its informal summary).

import Definitions.Def_StabilityDichotomies_Approximability_Core
open scoped Classical

namespace StabilityDichotomies.Solvability

/-- Theorem 4.1: bounded width characterizes stable approximation. -/
theorem stable_approximability_dichotomy (Γ : Language) :
    Xor
      (BoundedWidth Γ ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            ∃ A : Solver Γ, Approximates A ε ∧
              ∀ (V : Type) [Fintype V] (I : Instance Γ V),
                Satisfiable I → 2 ≤ Fintype.card V →
                  averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ))
      (¬ BoundedWidth Γ ∧
        ∃ ε c : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < c ∧
          ∃ N : Set ℕ, N.Infinite ∧
            ∀ A : Solver Γ, Approximates A ε →
              ∀ n ∈ N, ∃ I : Instance Γ (Fin n),
                Satisfiable I ∧ c * n ≤ averageSensitivity A I) := by sorry

end StabilityDichotomies.Solvability
