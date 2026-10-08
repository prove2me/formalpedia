-- Prove2me | Theorems.Thm_ProbMFG_Existence_lemma_3_9
-- name    : ProbMFG.Existence.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:02.460446+00:00
-- url     : https://prove2.me/theorems/94a25a46-6c8b-42fa-8845-fc41cd01f285
-- title:
--   Lemma 3.9 — stability of FBSDE solvability under approximation
-- statement:
--   Assume the original costs satisfy (A.1)–(A.7). Let $(f^n,g^n)$ satisfy the same assumptions for all $n\ge1$ with common positive parameters $\lambda',c'_L$, converge to $(f,g)$ uniformly on every bounded subset of the stated state, control, time and measure domains, and admit a solution of the corresponding McKean–Vlasov FBSDE for each $n$. Then
--   $$(3.1)\text{ for }(f,g)\text{ has a solution.}$$
--   This transfers existence from bounded-gradient approximations to the original model.
--
--   **Formalization Note** The approximating Hamiltonian and its minimizer are recomputed from $f^n$, as in the paper's proof. Uniform convergence is expressed by an epsilon threshold for every moment-bounded set.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2719, Lemma 3.9; https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_ProbMFG_Existence_Model
import Definitions.Def_ProbMFG_Existence_Solution

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

/-- Lemma 3.9: uniform local approximation of costs transfers solvability. -/
theorem lemma_3_9 {d m k : ℕ} (M : Model d m k) (lam cL : ℝ)
    (hA : M.Assumptions lam cL) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Fin m → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
    (fn : ℕ → ℝ≥0 → State d → Measure (State d) → Action k → ℝ)
    (gn : ℕ → State d → Measure (State d) → ℝ)
    (hParams : ∃ lam' cL' : ℝ, 0 < lam' ∧ 0 < cL' ∧
      ∀ n : ℕ, 1 ≤ n → ({ M with f := fn n, g := gn n } : Model d m k).Assumptions lam' cL')
    (hf : ∀ R ε : ℝ, 0 ≤ R → 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ t ≤ M.T, ∀ x μ a, IsP2 μ → ‖x‖ ≤ R → ‖a‖ ≤ R →
        (moment 2 μ).toReal ≤ R → |fn n t x μ a - M.f t x μ a| ≤ ε)
    (hg : ∀ R ε : ℝ, 0 ≤ R → 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ x μ, IsP2 μ → ‖x‖ ≤ R → (moment 2 μ).toReal ≤ R →
        |gn n x μ - M.g x μ| ≤ ε)
    (hSolutions : ∀ n : ℕ, 1 ≤ n →
      ∃ (X Y : StateProcess Ω d) (Z : NoiseProcess Ω d m),
        ({ M with f := fn n, g := gn n } : Model d m k).SolvesMKV P hW X Y Z) :
    ∃ (X Y : StateProcess Ω d) (Z : NoiseProcess Ω d m),
      M.SolvesMKV P hW X Y Z := by sorry

end ProbMFG.Existence
