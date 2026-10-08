-- Prove2me | Theorems.Thm_PrimalDualSubgrad_Stoch_theorem_7
-- name    : PrimalDualSubgrad.Stoch.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:53.548977+00:00
-- url     : https://prove2.me/theorems/ddf95d5b-05b4-4998-b3b7-78c4d9cf8078
-- title:
--   Theorem 7 — stochastic simple averages: $\mathbb E\,\varphi(\bar x_k) - \varphi^* \le \frac{\hat\beta_{k+1}}{k+1}(\gamma d(x^*) + \frac{L^2}{2\sigma\gamma})$
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, and $Q \subseteq E$ closed and convex with a prox-function $d$ (convexity parameter $\sigma > 0$, prox-center $x_0$, $d(x_0) = 0$) and argmin map $\pi_\beta(s) = \arg\min_{x \in Q}\{-\langle s, x\rangle + \beta d(x)\}$. Let $(\Xi, \mu)$ be a probability space, $f : Q \times \Xi \to \mathbb R$ a cost and $f'$ a stochastic oracle satisfying the standing assumptions of §6: $f(x,\cdot)$ is integrable, $f(\cdot,\xi)$ is convex on $Q$, $f'(x,\xi)$ is a subgradient of $f(\cdot,\xi)$ at $x$ with $\|f'(x,\xi)\|_* \le L$, and $f, f'$ are jointly measurable. Let $x^*$ minimize $\varphi(x) = \mathbb E_\xi f(x,\xi)$ over $Q$, and $\varphi^* = \varphi(x^*)$.
--
--   Fix $\gamma > 0$ and let $\{x_k\}_{k \ge 0}$ be the random points of the method of stochastic simple averages (6.3), driven by independent copies $\xi_0, \xi_1, \dots$ of $\xi$. Then for every $k \ge 0$
--   $$\mathbb E_{\boldsymbol\xi_k}\Big(\varphi\Big(\frac{1}{k+1}\sum_{i=0}^k x_i\Big)\Big) - \varphi^* \ \le\ \frac{\hat\beta_{k+1}}{k+1}\Big(\gamma\, d(x^*) + \frac{L^2}{2\sigma\gamma}\Big),$$
--   where $\hat\beta$ is the sequence (2.19) and $\boldsymbol\xi_k = (\xi_0, \dots, \xi_k)$.
--
--   Since $\hat\beta_{k+1}$ grows like $\sqrt{2k}$ (Lemma 3), the averaged point is an $O(1/\sqrt k)$-accurate solution of the stochastic problem in expectation, with no bound on the diameter of $Q$ required.
--
--   **Formalization Note** $\mathbb E_{\boldsymbol\xi_k}$ is the integral over $\Xi^{k+1}$ against the product measure $\mu^{\otimes(k+1)}$. Joint measurability of $f$ and $f'$ is added to the paper's assumptions so that every expectation is a genuine integral.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), p. 27, Theorem 7

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
import Definitions.Def_PrimalDualSubgrad_Stoch_SSA

namespace PrimalDualSubgrad.Stoch

open Finset MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- Nesterov 2009, p. 27, Theorem 7: for the Method of Stochastic Simple Averages (6.3), for every
`k ≥ 0`, `E_{ξ^k} φ((1/(k+1)) Σ_{i=0}^k x_i) − φ* ≤ β̂_{k+1}/(k+1) · (γ d(x*) + L²/(2σγ))`, where
`E_{ξ^k}` integrates against `μ^{⊗(k+1)}`, the law of `k + 1` i.i.d. copies of `ξ`. -/
theorem theorem_7 (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (f : E → Ξ → ℝ) (f' : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : StochOracle Q μ f f' L)
    (xstar : E) (hxstar : xstar ∈ Q)
    (hmin : ∀ x ∈ Q, expectedCost μ f xstar ≤ expectedCost μ f x)
    (γ : ℝ) (hγ : 0 < γ) (k : ℕ) :
    ∫ ω, expectedCost μ f ((1 / ((k : ℝ) + 1)) • ∑ i ∈ range (k + 1), ssaRun π γ x0 f' (padSample ω) i)
        ∂(sampleLaw μ k) - expectedCost μ f xstar
      ≤ betaHat (k + 1) / ((k : ℝ) + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ)) := by sorry

end PrimalDualSubgrad.Stoch
