-- Prove2me | Theorems.Thm_PrimalDualSubgrad_Stoch_gap_lower_bound
-- name    : PrimalDualSubgrad.Stoch.gap_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:36.726167+00:00
-- url     : https://prove2.me/theorems/2b93901c-849a-4f27-90cd-995ae414cab0
-- title:
--   §6, display after (6.5) — $\frac{1}{k+1}\tilde\delta_k(D) \ge \frac{1}{k+1}\sum_i[f(\tilde x_i,\tilde\xi_i) - f(x^*,\tilde\xi_i)]$ for $D \ge d(x^*)$
-- statement:
--   Under the standing assumptions of §6, let $x^* \in Q$ be a minimizer of $\varphi(x) = \mathbb E_\xi f(x,\xi)$ over $Q$. Fix $\gamma > 0$ and a realization $\tilde\xi_0, \tilde\xi_1, \dots$ of the samples, let $\tilde x_i$ be the points of the method of stochastic simple averages (6.3) on it and $\tilde\delta_k(D)$ the gap (6.4). If $D \ge d(x^*)$, then for every $k \ge 0$
--   $$\frac{1}{k+1}\tilde\delta_k(D) \ \ge\ \frac{1}{k+1}\sum_{i=0}^k \langle f'(\tilde x_i, \tilde\xi_i), \tilde x_i - x^*\rangle \ \ge\ \frac{1}{k+1}\sum_{i=0}^k \big[f(\tilde x_i, \tilde\xi_i) - f(x^*, \tilde\xi_i)\big].$$
--
--   The gap of a run therefore dominates the average excess cost of the visited points against the optimum on the same samples; this is the second step of the proof of Theorem 7.
--
--   **Formalization Note** $S_k = k+1$. The two inequalities are stated as a conjunction, each written with $\le$.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), §6, display after (6.5), p. 26

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
import Definitions.Def_PrimalDualSubgrad_Stoch_SSA

namespace PrimalDualSubgrad.Stoch

open Finset MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- Nesterov 2009, §6, display after (6.5), p. 26: for `D ≥ d(x*)` and every sample path,
`(1/S_k) δ̃_k(D) ≥ (1/(k+1)) Σ ⟨f'(x̃_i, ξ̃_i), x̃_i − x*⟩ ≥ (1/(k+1)) Σ [f(x̃_i, ξ̃_i) − f(x*, ξ̃_i)]`
(the two inequalities as a conjunction, the first written right-to-left). -/
theorem gap_lower_bound (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (f : E → Ξ → ℝ) (f' : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : StochOracle Q μ f f' L)
    (xstar : E) (hxstar : xstar ∈ Q)
    (hmin : ∀ x ∈ Q, expectedCost μ f xstar ≤ expectedCost μ f x)
    (γ : ℝ) (hγ : 0 < γ) (ω : ℕ → Ξ) (k : ℕ) (D : ℝ) (hD : d xstar ≤ D) :
    1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1), f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i - xstar)
        ≤ 1 / ((k : ℝ) + 1) * gap Q d (fun i => f' (ssaRun π γ x0 f' ω i) (ω i)) (ssaRun π γ x0 f' ω) k D ∧
      1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1), (f (ssaRun π γ x0 f' ω i) (ω i) - f xstar (ω i))
        ≤ 1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1), f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i - xstar) := by sorry

end PrimalDualSubgrad.Stoch
