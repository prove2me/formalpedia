-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_nonwidth_approximation_lower
-- name    : StabilityDichotomies.Solvability.nonwidth_approximation_lower
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T06:26:02.2018+00:00
-- url     : https://prove2.me/theorems/24c8419c-c92b-4c44-8a72-1892327aab70
-- title:
--   The non-bounded-width approximation lower branch
-- statement:
--   If the finite Boolean constraint language $\Gamma$ does not have bounded width, there exist $0<\varepsilon_\Gamma\le1$, $c_\Gamma>0$, and an infinite set $N_\Gamma\subseteq\mathbb N$ such that, for every solver that $(1-\varepsilon_\Gamma)$-approximates $\operatorname{CSP}(\Gamma)$ and every $n\in N_\Gamma$, some satisfiable instance on $n$ variables has average sensitivity at least $c_\Gamma n$. This is the lower branch of Theorem 4.1 under the platform’s semantic solver model.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Theorem 4.1(ii), p.16.

import Definitions.Def_StabilityDichotomies_Approximability_Core
noncomputable section
open scoped Classical

namespace StabilityDichotomies.Solvability
theorem nonwidth_approximation_lower (Γ : Language) (hΓ : ¬ BoundedWidth Γ) :
    ∃ ε c : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < c ∧
      ∃ N : Set ℕ, N.Infinite ∧
        ∀ A : Solver Γ, Approximates A ε →
          ∀ n ∈ N, ∃ I : Instance Γ (Fin n),
            Satisfiable I ∧ c * n ≤ averageSensitivity A I := by
  sorry

end StabilityDichotomies.Solvability
