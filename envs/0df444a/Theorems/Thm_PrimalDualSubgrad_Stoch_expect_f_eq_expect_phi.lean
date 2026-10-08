-- Prove2me | Theorems.Thm_PrimalDualSubgrad_Stoch_expect_f_eq_expect_phi
-- name    : PrimalDualSubgrad.Stoch.expect_f_eq_expect_phi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:36.243081+00:00
-- url     : https://prove2.me/theorems/4d54df75-d320-43b9-aaa4-de8f7cedbd34
-- title:
--   §6, p. 27 — $x_i$ is independent of $\xi_i$, hence $\mathbb E_{\xi_k} f(x_i,\xi_i) = \mathbb E_{\xi_k}\varphi(x_i)$
-- statement:
--   Under the standing assumptions of §6, fix $\gamma > 0$ and $0 \le i \le k$. Let $\boldsymbol\xi_k = (\xi_0, \dots, \xi_k)$ be $k+1$ independent copies of $\xi \sim \mu$ and $x_i = x_i(\xi_0, \dots, \xi_{i-1})$ the $i$-th point of the method of stochastic simple averages (6.3). Then
--   $$\mathbb E_{\boldsymbol\xi_k}\big(f(x_i, \xi_i)\big) = \mathbb E_{\boldsymbol\xi_k}\big(\varphi(x_i)\big), \qquad \varphi(x) = \mathbb E_\xi f(x, \xi).$$
--
--   The point $x_i$ is built from the earlier samples only, so it is independent of $\xi_i$; the identity replaces the sampled cost by the true objective.
--
--   **Formalization Note** $\mathbb E_{\boldsymbol\xi_k}$ is the integral over $\Xi^{k+1}$ against $\mu^{\otimes(k+1)}$.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), §6, p. 27, first display

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
import Definitions.Def_PrimalDualSubgrad_Stoch_SSA

namespace PrimalDualSubgrad.Stoch

open Finset MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- Nesterov 2009, §6, p. 27, first display: for `i ≤ k`,
`E_{ξ^k} f(x_i, ξ_i) = E_{ξ^k} φ(x_i)` (the iterate `x_i` depends on `ξ_0, …, ξ_{i-1}` only). -/
theorem expect_f_eq_expect_phi (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (f : E → Ξ → ℝ) (f' : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : StochOracle Q μ f f' L)
    (γ : ℝ) (hγ : 0 < γ) (k i : ℕ) (hi : i ≤ k) :
    ∫ ω, f (ssaRun π γ x0 f' (padSample ω) i) (padSample ω i) ∂(sampleLaw μ k)
      = ∫ ω, expectedCost μ f (ssaRun π γ x0 f' (padSample ω) i) ∂(sampleLaw μ k) := by sorry

end PrimalDualSubgrad.Stoch
