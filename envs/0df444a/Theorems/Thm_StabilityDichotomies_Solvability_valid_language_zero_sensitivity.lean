-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_valid_language_zero_sensitivity
-- name    : StabilityDichotomies.Solvability.valid_language_zero_sensitivity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:22:29.308755+00:00
-- url     : https://prove2.me/theorems/aac7b3a8-fbea-4cf3-86b1-b9708fc82d52
-- title:
--   Constant-valid languages have zero-sensitivity exact solvers
-- statement:
--   Let $\Gamma$ be a Boolean constraint language in which every relation contains the constant tuple $b$, and let $\varepsilon\ge0$. There exists a solver that $(1-\varepsilon)$-approximates every satisfiable instance and has average sensitivity exactly zero on every instance. The solver is the constant assignment $b$; in fact it satisfies every constraint. This proves the constant-valid upper-bound cases of Theorems 3.1 and 4.1.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proofs of Theorems 3.1 and 4.1, pp.11 and 15–16.

import Definitions.Def_StabilityDichotomies_Approximability_Core
import Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
noncomputable section
open scoped Classical BigOperators ENNReal

namespace StabilityDichotomies.Solvability
theorem valid_language_zero_sensitivity (Γ : Language) (b : Bool) (hv : Valid Γ b)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ A : Solver Γ, Approximates A ε ∧
      ∀ (V : Type) [Fintype V] (I : Instance Γ V), averageSensitivity A I = 0 := by sorry
end StabilityDichotomies.Solvability
