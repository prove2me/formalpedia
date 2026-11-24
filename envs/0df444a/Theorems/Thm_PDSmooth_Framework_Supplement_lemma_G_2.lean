-- Prove2me | Theorems.Thm_PDSmooth_Framework_Supplement_lemma_G_2
-- name    : PDSmooth.Framework.Supplement.lemma_G_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T07:53:42.537605+00:00
-- url     : https://prove2.me/theorems/abd8dbb3-820d-4021-b8a1-44a9895ae43c
-- title:
--   Lemma G.2, p. 41 — the weights (5.23) and (5.27) give A_t = (t + 2)²/4 and A_t = (1 + √θ)^t, and satisfy (G.3)
-- statement:
--   Let $\bar L>0$, $\mu\ge0$ and $\theta:=\mu/\bar L$, and let $A_t=\sum_{i=0}^t\alpha_i$.
--
--   1. If $\mu=0$ and $\alpha_0=1$, $\alpha_t=(2t+3)/4$ for $t\ge1$ (5.23), then $A_t=(t+2)^2/4$ for all $t\ge0$.
--   2. If $\mu>0$ and $\alpha_0=1$, $\alpha_t=(1+\sqrt\theta)^{t-1}\sqrt\theta$ for $t\ge1$ (5.27), then $A_t=(1+\sqrt\theta)^t$ for all $t\ge0$.
--
--   $$
--   A_t=\begin{cases}(t+2)^2/4,&\mu=0,\\ (1+\sqrt\theta)^t,&\mu>0,\end{cases}\qquad\forall t\ge0. \tag{G.8}
--   $$
--
--   In both cases the condition (G.3), $(A_t\mu+\bar L)A_{t+1}\ge\bar L\alpha_{t+1}^2$ for all $t\ge0$, is satisfied.
--
--   The lemma confirms that the weight choices of Theorems 5.1 and 5.2 meet the hypothesis of Lemma G.1 and computes the accumulated weights that appear in the rates.
--
--   **Formalization Note** $\bar L>0$ is the input requirement of Algorithm 2; $(1+\sqrt\theta)^{t-1}$ is used only for $t\ge1$.
--
--   Differences from the source:
--   - encoding: L̄ > 0 implicit (θ := μ/L̄; L̄ ≥ L_h is an input of Algorithm 2) → hypothesis 0 < L̄; reason: a nondegeneracy condition the page presupposes; it excludes only the undefined case
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 41, Lemma G.2, (G.8), with (5.23), (5.27) (p. 24) and (G.3) (p. 40)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Supplement_Alg2

namespace PDSmooth.Framework.Supplement

/-- Lemma G.2, p. 41: for `L̄ > 0`, the weights (5.23) (`μ = 0`: `α₀ = 1`, `α_t = (2t + 3)/4`) give
`A_t = (t + 2)²/4`, the weights (5.27) (`μ > 0`: `α₀ = 1`, `α_t = (1 + √θ)^{t−1}√θ`, `θ = μ/L̄`) give
`A_t = (1 + √θ)^t` (G.8), and in both cases `(A_tμ + L̄)A_{t+1} ≥ L̄α²_{t+1}` for all `t ≥ 0` (G.3). -/
theorem lemma_G_2 (μ Lbar : ℝ) (hLbar : 0 < Lbar) (α : ℕ → ℝ) :
    (μ = 0 → α 0 = 1 → (∀ t : ℕ, 1 ≤ t → α t = (2 * (t : ℝ) + 3) / 4) →
      (∀ t : ℕ, accW α t = ((t : ℝ) + 2) ^ 2 / 4) ∧
      ∀ t : ℕ, Lbar * α (t + 1) ^ 2 ≤ (accW α t * μ + Lbar) * accW α (t + 1)) ∧
    (0 < μ → α 0 = 1 →
      (∀ t : ℕ, 1 ≤ t → α t = (1 + Real.sqrt (μ / Lbar)) ^ (t - 1) * Real.sqrt (μ / Lbar)) →
      (∀ t : ℕ, accW α t = (1 + Real.sqrt (μ / Lbar)) ^ t) ∧
      ∀ t : ℕ, Lbar * α (t + 1) ^ 2 ≤ (accW α t * μ + Lbar) * accW α (t + 1)) := by sorry

end PDSmooth.Framework.Supplement
