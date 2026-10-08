-- Prove2me | Theorems.Thm_PrimalDualSubgrad_Stoch_eq_6_6
-- name    : PrimalDualSubgrad.Stoch.eq_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:04.841164+00:00
-- url     : https://prove2.me/theorems/2e2acc32-e1ff-4720-895e-088ad8f0b9bd
-- title:
--   (6.6) — $\mathbb E_{\xi_k}(\frac{1}{k+1}\delta_k(D)) \ge \frac{1}{k+1}\sum_i \mathbb E_{\xi_k} f(x_i,\xi_i) - \varphi^*$
-- statement:
--   Under the standing assumptions of §6, let $x^*$ be a minimizer of $\varphi$ over $Q$ and $\varphi^* = \varphi(x^*)$. Fix $\gamma > 0$, $k \ge 0$ and $D \ge d(x^*)$. Let $\boldsymbol\xi_k = (\xi_0, \dots, \xi_k)$ be $k+1$ independent copies of $\xi \sim \mu$, let $x_0, \dots, x_k$ be the random points of the method of stochastic simple averages (6.3) driven by them, and let $\delta_k(D)$ be the random gap (6.4) of the run. Then
--   $$\mathbb E_{\boldsymbol\xi_k}\Big(\frac{1}{k+1}\delta_k(D)\Big) \ \ge\ \frac{1}{k+1}\sum_{i=0}^k \mathbb E_{\boldsymbol\xi_k}\big(f(x_i, \xi_i)\big) - \varphi^*.$$
--
--   This is the pathwise lower bound of the gap taken in expectation, using that each $\xi_i$ has the law of $\xi$; it is the third step of the proof of Theorem 7.
--
--   **Formalization Note** $\mathbb E_{\boldsymbol\xi_k}$ is the integral over $\Xi^{k+1}$ against the product measure $\mu^{\otimes(k+1)}$; the run is evaluated on the sample extended by a padding that it never reads. $S_k = k+1$. The inequality is written with $\le$, sides swapped.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), §6, (6.6), p. 26

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
import Definitions.Def_PrimalDualSubgrad_Stoch_SSA

namespace PrimalDualSubgrad.Stoch

open Finset MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- Nesterov 2009, §6, (6.6), p. 26: for `D ≥ d(x*)`,
`E_{ξ^k}((1/S_k) δ_k(D)) ≥ (1/(k+1)) Σ_{i=0}^k E_{ξ^k} f(x_i, ξ_i) − φ*`, where `E_{ξ^k}` integrates
against `μ^{⊗(k+1)}` (written with `≤`, sides swapped). -/
theorem eq_6_6 (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (f : E → Ξ → ℝ) (f' : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : StochOracle Q μ f f' L)
    (xstar : E) (hxstar : xstar ∈ Q)
    (hmin : ∀ x ∈ Q, expectedCost μ f xstar ≤ expectedCost μ f x)
    (γ : ℝ) (hγ : 0 < γ) (k : ℕ) (D : ℝ) (hD : d xstar ≤ D) :
    1 / ((k : ℝ) + 1) * ∑ i ∈ range (k + 1),
          ∫ ω, f (ssaRun π γ x0 f' (padSample ω) i) (padSample ω i) ∂(sampleLaw μ k)
        - expectedCost μ f xstar
      ≤ ∫ ω, 1 / ((k : ℝ) + 1) *
          gap Q d (fun i => f' (ssaRun π γ x0 f' (padSample ω) i) (padSample ω i)) (ssaRun π γ x0 f' (padSample ω)) k D
          ∂(sampleLaw μ k) := by sorry

end PrimalDualSubgrad.Stoch
