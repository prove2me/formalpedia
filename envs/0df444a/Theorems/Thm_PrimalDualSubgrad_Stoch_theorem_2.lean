-- Prove2me | Theorems.Thm_PrimalDualSubgrad_Stoch_theorem_2
-- name    : PrimalDualSubgrad.Stoch.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:26.632338+00:00
-- url     : https://prove2.me/theorems/10a9ecb6-4200-4801-bb0f-fc6a7876cbdf
-- title:
--   Theorem 2 — simple dual averages: $\delta_k(D) \le \hat\beta_{k+1}(\gamma D + L_k^2/(2\sigma\gamma))$ and bounded iterates
-- statement:
--   Let $d$ be a prox-function of the closed convex set $Q$ with convexity parameter $\sigma > 0$ and prox-center $x_0$, let $\pi_\beta$ be its argmin map, and let $\hat\beta_k$ be the sequence (2.19). Fix $\gamma > 0$ and any sequence $g_0, g_1, \dots \in E^*$, and let $x_0, x_1, \dots$ be the points of the method of simple dual averages (2.21). Write $L_k = \max_{0\le i\le k}\|g_i\|_*$ and $\delta_k(D) = \max\{\sum_{i=0}^k \langle g_i, x_i - x\rangle : x \in Q,\ d(x) \le D\}$. Then:
--
--   1. for every $k \ge 0$ and every $D \ge 0$,
--   $$\delta_k(D) \le \hat\beta_{k+1}\Big(\gamma D + \frac{L_k^2}{2\sigma\gamma}\Big);$$
--   2. if $x^* \in Q$ satisfies $\langle g_i, x_i - x^*\rangle \ge 0$ for all $i \ge 0$ (condition (2.8)), then for every $k \ge 0$
--   $$\|x_k - x^*\|^2 \le \frac{2}{\sigma} d(x^*) + \frac{L_k^2}{\sigma^2\gamma^2}.$$
--
--   The first bound is the deterministic estimate that, applied along every sample path, controls the stochastic method of §6; the second shows that the points of the method stay bounded even when $Q$ is unbounded.
--
--   **Formalization Note** The paper's remark $S_k = k+1$ (the sum of the unit weights) is omitted, as it holds by definition. The answers $g_i$ are arbitrary data rather than $\mathcal G(x_i)$; the theorem is stated for every such sequence.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), p. 11, Theorem 2

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
import Definitions.Def_PrimalDualSubgrad_Stoch_SDA

namespace PrimalDualSubgrad.Stoch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Nesterov 2009, p. 11, Theorem 2, for the Method of Simple Dual Averages (2.21) driven by an
arbitrary answer sequence `g`: (1) `δ_k(D) ≤ β̂_{k+1}(γD + L_k²/(2σγ))` for all `k ≥ 0`, `D ≥ 0`;
(2) under (2.8), `‖x_k − x*‖² ≤ (2/σ)d(x*) + L_k²/(σ²γ²)` for all `k ≥ 0`. (`S_k = k + 1` is omitted:
it holds by definition with unit weights.) -/
theorem theorem_2 (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π) (γ : ℝ) (hγ : 0 < γ)
    (g : ℕ → StrongDual ℝ E) :
    (∀ k : ℕ, ∀ D : ℝ, 0 ≤ D →
      gap Q d g (sdaPoints π γ x0 g) k D
        ≤ betaHat (k + 1) * (γ * D + maxDualNorm g k ^ 2 / (2 * σ * γ))) ∧
    (∀ xstar ∈ Q, (∀ i : ℕ, 0 ≤ g i (sdaPoints π γ x0 g i - xstar)) →
      ∀ k : ℕ, ‖sdaPoints π γ x0 g k - xstar‖ ^ 2
        ≤ 2 / σ * d xstar + maxDualNorm g k ^ 2 / (σ ^ 2 * γ ^ 2)) := by sorry

end PrimalDualSubgrad.Stoch
