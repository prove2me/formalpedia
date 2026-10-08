-- Prove2me | Theorems.Thm_ProbMFG_Existence_theorem_2_2
-- name    : ProbMFG.Existence.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:24.285401+00:00
-- url     : https://prove2.me/theorems/b70f3c33-9b72-4403-9620-e488edd39787
-- title:
--   Theorem 2.2 — sufficient maximum principle with a control gap
-- statement:
--   Under (A.1)–(A.4), let $\mu$ be a measurable bounded flow of probability measures of finite second moment. Suppose $(X,Y,Z)$ solves the frozen-flow FBSDE (2.13) with the integrability in (2.14). For any admissible control $\beta$ and its controlled state $U$, let $\hat a_t=\hat a(t,X_t,\mu_t,Y_t)$. Then
--   $$J(\hat a;\mu)+\lambda\mathbb E\int_0^T\|\beta_t-\hat a_t\|^2\,dt\le J(\beta;\mu).$$
--   The inequality certifies optimality and supplies the quantitative separation used in later comparisons.
--
--   **Formalization Note** Admissibility is Peng's progressive $L^2$ predicate. The nonnegative gap integral is converted to a real number; its finiteness follows from (2.2), (2.14), and Lemma 2.1. The real costs are finite under the stated assumptions.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2711, Theorem 2.2; https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_ProbMFG_Existence_Model
import Definitions.Def_ProbMFG_Existence_Solution

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

/-- Theorem 2.2: the sufficient stochastic maximum principle for a frozen flow,
including its quantitative control gap. -/
theorem theorem_2_2 {d m k : ℕ} (M : Model d m k) (lam cL : ℝ)
    (hlam : 0 < lam) (hcL : 0 < cL)
    (hA1 : M.A1) (hA2 : M.A2 lam cL) (hA3 : M.A3) (hA4 : M.A4 cL)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Fin m → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
    (μ : ℝ≥0 → Measure (State d)) (X Y : StateProcess Ω d)
    (Z : NoiseProcess Ω d m) (hXYZ : M.SolvesFrozen P hW μ X Y Z)
    (β : ℝ≥0 → Ω → Action k)
    (hβ : Peng1990.SMP.L2F (ReflectedBSDE.Existence.augmentedFiltration P hW) P M.T β)
    (U : StateProcess Ω d) (hU : M.IsControlled P hW μ M.x₀ U β) :
    M.cost P μ X (fun t ω => M.alphaHat t (X t ω) (μ t) (Y t ω)) +
      lam * (∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) M.T,
        ‖β t.toNNReal ω - M.alphaHat t.toNNReal (X t.toNNReal ω)
          (μ t.toNNReal) (Y t.toNNReal ω)‖ₑ ^ 2 ∂volume ∂P).toReal ≤
      M.cost P μ U β := by sorry

end ProbMFG.Existence
