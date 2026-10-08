-- Prove2me | Theorems.Thm_ProbMFG_Existence_theorem_3_2
-- name    : ProbMFG.Existence.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:43.663764+00:00
-- url     : https://prove2.me/theorems/cee557f5-430b-4eeb-bd9b-ede2ec8101f5
-- title:
--   Theorem 3.2 — existence and Lipschitz FBSDE value function
-- statement:
--   Under assumptions (A.1)–(A.7), the McKean–Vlasov FBSDE (3.1), whose measure argument is the law of its forward state, has a solution. For every solution $(X,Y,Z)$ there is a function $u:[0,T]\times\mathbb R^d\to\mathbb R^d$ and a constant $c\ge0$ such that, for all $t\in[0,T]$ and $x,x'\in\mathbb R^d$,
--   $$\|u(t,x)\|\le c(1+\|x\|),\qquad\|u(t,x)-u(t,x')\|\le c\|x-x'\|,\qquad Y_t=u(t,X_t)\quad\text{a.s. simultaneously for all }t.$$
--   Furthermore, for every real $\ell\ge1$, $\mathbb E[\sup_{0\le t\le T}\|X_t\|^\ell]<\infty$.
--
--   The value function provides a state-dependent feedback representation and its regularity is used in the paper's approximate-Nash result.
--
--   **Formalization Note** The solution uses Euclidean norms, a genuine law $\mathcal L(X_t)$, an augmented Brownian filtration and the square-integrable solution class (2.14). The constant $c$ is chosen separately for each solution.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2714, Theorem 3.2 and (3.3); https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_ProbMFG_Existence_Model
import Definitions.Def_ProbMFG_Existence_Solution

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

/-- Theorem 3.2: existence, a Lipschitz FBSDE value function for every
solution, and finite moments of every order at least one. -/
theorem theorem_3_2 {d m k : ℕ} (M : Model d m k) (lam cL : ℝ)
    (hA : M.Assumptions lam cL) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Fin m → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W) :
    (∃ (X Y : StateProcess Ω d) (Z : NoiseProcess Ω d m),
      M.SolvesMKV P hW X Y Z) ∧
    (∀ (X Y : StateProcess Ω d) (Z : NoiseProcess Ω d m),
      M.SolvesMKV P hW X Y Z →
      ∃ (u : ℝ≥0 → State d → State d) (c : ℝ), 0 ≤ c ∧
        (∀ t ≤ M.T, ∀ x x' : State d,
          ‖u t x‖ ≤ c * (1 + ‖x‖) ∧
          ‖u t x - u t x'‖ ≤ c * ‖x - x'‖) ∧
        ∀ᵐ ω ∂P, ∀ t ≤ M.T, Y t ω = u t (X t ω)) ∧
    (∀ (X Y : StateProcess Ω d) (Z : NoiseProcess Ω d m),
      M.SolvesMKV P hW X Y Z →
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∫⁻ ω, ⨆ t ≤ M.T, ‖X t ω‖ₑ ^ ℓ ∂P < ⊤) := by sorry

end ProbMFG.Existence
