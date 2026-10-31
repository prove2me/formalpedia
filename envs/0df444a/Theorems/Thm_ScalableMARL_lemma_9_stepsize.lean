-- Prove2me | Theorems.Thm_ScalableMARL_lemma_9_stepsize
-- name    : ScalableMARL.lemma_9_stepsize
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:36.50919+00:00
-- url     : https://prove2.me/theorems/1de3efee-ad69-45e5-9894-ef729d375df2
-- title:
--   Lemma 9 — bounds on the step-size products $\beta_{k,t}$ and $\tilde\beta_{k,t}$
-- statement:
--   Let $\sigma\in(0,1)$ and let $\tau\ge1$ be an integer (as in Assumption 3), and let $\alpha_t=h/(t+t_0)$ with
--   $$t_0\ge h>\frac2\sigma,\qquad t_0\ge4\sigma h,\qquad t_0\ge\tau .$$
--   With $\beta_{k,t}=\alpha_k\prod_{\ell=k+1}^{t-1}(1-\alpha_\ell\sigma)$ and $\tilde\beta_{k,t}=\prod_{\ell=k+1}^{t-1}(1-\alpha_\ell\sigma)$:
--
--   1. for all $k,t$: $\displaystyle\beta_{k,t}\le\frac{h}{k+t_0}\Big(\frac{k+1+t_0}{t+t_0}\Big)^{\sigma h}$ and $\displaystyle\tilde\beta_{k,t}\le\Big(\frac{k+1+t_0}{t+t_0}\Big)^{\sigma h}$;
--   2. for all $t$: $\displaystyle\sum_{k=1}^{t-1}\beta_{k,t}^2\le\frac{2h}{\sigma}\,\frac{1}{t+t_0}$;
--   3. for all $t$: $\displaystyle\sum_{k=\tau}^{t-1}\beta_{k,t}\sum_{\ell=k-\tau+1}^{k-1}\alpha_\ell\le\frac{8h\tau}{\sigma}\,\frac{1}{t+t_0}$.
--
--   These elementary estimates control the transient and the noise accumulation of the critic recursion in the proof of Theorem 5.
--
--   **Formalization Note** $(\cdot)^{\sigma h}$ is the real power `Real.rpow`. Sums over empty ranges are $0$ and empty products are $1$.
--
--   Differences from the source:
--   - reading: σ and τ unqualified in Lemma 9 → σ ∈ (0, 1) and an integer τ ≥ 1; reason: they are the σ, τ of Assumption 3, standing throughout §4.1
--   - generalization: (a) for the pairs k < t used in the proof → (a) for all k, t ∈ ℕ; reason: for k ≥ t the products are empty and the bound still holds; restricting to k < t gives the page's claim
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 17, Lemma 9 (a)–(c)

import Mathlib
import Definitions.Def_ScalableMARL_StepSizes

namespace ScalableMARL

/-- **Lemma 9 (step-size products).** Qu, Wierman & Li, arXiv:1912.02906v3, p. 17, Lemma 9. Let
`α_t = h/(t + t₀)`, `β_{k,t} = α_k ∏_{ℓ=k+1}^{t−1}(1 − α_ℓ σ)` and `β̃_{k,t} = ∏_{ℓ=k+1}^{t−1}(1 − α_ℓ σ)`.
If `t₀ ≥ h > 2/σ`, `t₀ ≥ 4σh` and `t₀ ≥ τ`, then
(a) `β_{k,t} ≤ (h/(k + t₀))((k + 1 + t₀)/(t + t₀))^{σh}` and `β̃_{k,t} ≤ ((k + 1 + t₀)/(t + t₀))^{σh}`;
(b) `Σ_{k=1}^{t−1} β_{k,t}² ≤ (2h/σ)/(t + t₀)`;
(c) `Σ_{k=τ}^{t−1} β_{k,t} Σ_{ℓ=k−τ+1}^{k−1} α_ℓ ≤ (8hτ/σ)/(t + t₀)`.

**Formalization Note.** `σ ∈ (0, 1)` and the integer `τ ≥ 1` are those of Assumption 3 (p. 12).
(a) is stated for all `k, t ∈ ℕ`, (b) and (c) for all `t`. The exponent `σh` is a real power. -/
theorem lemma_9_stepsize (σ h t₀ : ℝ) (τ : ℕ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hτ : 1 ≤ τ)
    (hht : h ≤ t₀) (hh : 2 / σ < h) (h4 : 4 * σ * h ≤ t₀) (hτt : (τ : ℝ) ≤ t₀) :
    (∀ k t : ℕ,
      betaKT h t₀ σ k t ≤ h / (k + t₀) * ((k + 1 + t₀) / (t + t₀)) ^ (σ * h) ∧
      betaTildeKT h t₀ σ k t ≤ ((k + 1 + t₀) / (t + t₀)) ^ (σ * h)) ∧
    (∀ t : ℕ, ∑ k ∈ Finset.Ico 1 t, betaKT h t₀ σ k t ^ 2 ≤ 2 * h / σ * (1 / (t + t₀))) ∧
    (∀ t : ℕ, ∑ k ∈ Finset.Ico τ t,
        betaKT h t₀ σ k t * ∑ ℓ ∈ Finset.Ico (k + 1 - τ) k, h / (ℓ + t₀) ≤
      8 * h * τ / σ * (1 / (t + t₀))) := by sorry

end ScalableMARL
