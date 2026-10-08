-- Prove2me | Theorems.Thm_PrimalDualSubgrad_Stoch_average_jensen
-- name    : PrimalDualSubgrad.Stoch.average_jensen
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:13.223992+00:00
-- url     : https://prove2.me/theorems/d40bb922-b7d1-4c43-970d-74fd0ac69524
-- title:
--   §6, p. 27 — $\frac{1}{k+1}\sum_i\mathbb E f(x_i,\xi_i) = \frac{1}{k+1}\sum_i\mathbb E\varphi(x_i) \ge \mathbb E\varphi(\bar x_k)$
-- statement:
--   Under the standing assumptions of §6, fix $\gamma > 0$ and $k \ge 0$. Let $\boldsymbol\xi_k = (\xi_0,\dots,\xi_k)$ be $k+1$ independent copies of $\xi \sim \mu$ and $x_0, \dots, x_k$ the random points of the method of stochastic simple averages (6.3). Then
--   $$\frac{1}{k+1}\sum_{i=0}^k \mathbb E_{\boldsymbol\xi_k}\big(f(x_i,\xi_i)\big) = \frac{1}{k+1}\sum_{i=0}^k \mathbb E_{\boldsymbol\xi_k}\big(\varphi(x_i)\big) \ \ge\ \mathbb E_{\boldsymbol\xi_k}\Big(\varphi\Big(\frac{1}{k+1}\sum_{i=0}^k x_i\Big)\Big).$$
--
--   The equality averages the previous identity; the inequality compares the average objective value with the objective at the average point. Together with (6.5) and (6.6) it yields Theorem 7.
--
--   **Formalization Note** The equality and the inequality are stated as a conjunction, the inequality written with $\le$. $\mathbb E_{\boldsymbol\xi_k}$ is the integral against $\mu^{\otimes(k+1)}$.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), §6, p. 27, display before Theorem 7

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
import Definitions.Def_PrimalDualSubgrad_Stoch_SSA

namespace PrimalDualSubgrad.Stoch

open Finset MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- Nesterov 2009, §6, p. 27, display before Theorem 7:
`(1/(k+1)) Σ E f(x_i, ξ_i) = (1/(k+1)) Σ E φ(x_i) ≥ E φ((1/(k+1)) Σ x_i)` (conjunction; the
inequality written with `≤`, sides swapped). -/
theorem average_jensen (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (f : E → Ξ → ℝ) (f' : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : StochOracle Q μ f f' L)
    (γ : ℝ) (hγ : 0 < γ) (k : ℕ) :
    1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1),
          ∫ ω, f (ssaRun π γ x0 f' (padSample ω) i) (padSample ω i) ∂(sampleLaw μ k)
        = 1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1),
          ∫ ω, expectedCost μ f (ssaRun π γ x0 f' (padSample ω) i) ∂(sampleLaw μ k) ∧
      ∫ ω, expectedCost μ f ((1 / ((k : ℝ) + 1)) • ∑ i ∈ range (k + 1), ssaRun π γ x0 f' (padSample ω) i)
          ∂(sampleLaw μ k)
        ≤ 1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1),
          ∫ ω, expectedCost μ f (ssaRun π γ x0 f' (padSample ω) i) ∂(sampleLaw μ k) := by sorry

end PrimalDualSubgrad.Stoch
