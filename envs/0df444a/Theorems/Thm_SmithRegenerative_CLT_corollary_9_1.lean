-- Prove2me | Theorems.Thm_SmithRegenerative_CLT_corollary_9_1
-- name    : SmithRegenerative.CLT.corollary_9_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:29.405+00:00
-- url     : https://prove2.me/theorems/63317282-a7c7-4778-8b07-3f89a6e84919
-- title:
--   Corollary 9·1 — (w_t − κ₁n_t)/(σ(t/μ₁)^{1/2}) and, if μ₂ < ∞, (w_t − (κ₁/μ₁)t)/(γt/μ₁)^{1/2} are asymptotically standard normal
-- statement:
--   Let $w_t$ be a cumulative process on a renewal process $t_1, t_2, \dots$ with $t_0 = 0$ and $w_0 = 0$, with cycle increments $y_n = \Delta_n w_t$, variation increments $\tilde y_n$, and $n_t$ the number of regenerations in $[0,t]$. Suppose $E(\Delta_n \tilde w_t)^2 < \infty$ and $\mu_1 = E t_1 < \infty$, and put
--   $$\kappa_1 = E \Delta_n w_t, \qquad \kappa_2 = E(\Delta_n w_t)^2, \qquad \sigma^2 = \kappa_2 - \kappa_1^2, \quad \sigma > 0.$$
--   Then:
--
--   1. for every real $\alpha$,
--   $$\lim_{t \to \infty} P\left\{ \frac{w_t - \kappa_1 n_t}{\sigma (t/\mu_1)^{1/2}} \le \alpha \right\} = \Phi(\alpha);$$
--   2. if in addition $\mu_2 = E t_1^2 < \infty$, and $\gamma = \operatorname{var} \Delta_n(w_t - \kappa_1 \mu_1^{-1} t) = \operatorname{var}(y_1 - (\kappa_1/\mu_1) t_1)$ is positive, then for every real $\alpha$,
--   $$\lim_{t \to \infty} P\left\{ \frac{w_t - (\kappa_1/\mu_1) t}{(\gamma t/\mu_1)^{1/2}} \le \alpha \right\} = \Phi(\alpha).$$
--
--   The second assertion is the central limit theorem for renewal-reward processes with a deterministic centring; applied to $w_t = n_t$ it gives Feller's central limit theorem for renewal processes.
--
--   **Formalization Note** $\sigma > 0$ and $\gamma > 0$ are implicit in the paper, which divides by $\sigma$ and $\sqrt\gamma$. The two assertions are the two conjuncts of the statement.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 30, Corollary 9·1 (5·4·8)–(5·4·9)

import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), Corollary 9·1, p. 30: "If `w_t` is a general cumulative process for which
`E(Δ_n w̃_t)² < ∞`, `κ₁ ≡ EΔ_n w_t`, `κ₂ ≡ E(Δ_n w_t)² < ∞`, and `σ² ≡ κ₂ − κ₁²`, then provided
`μ₁ < ∞`, `lim_{t=∞} P{(w_t − κ₁n_t)/(σ(t/μ₁)^{1/2}) ≤ α} = Φ(α)` (5·4·8). If, in addition,
`μ₂ < ∞`, then `lim_{t=∞} P{(w_t − (κ₁/μ₁)t)/((γt/μ₁)^{1/2}) ≤ α} = Φ(α)` (5·4·9), where
`γ = var Δ_n(w_t − κ₁μ₁⁻¹t)`."

For a cumulative process with `t₀ = 0`, `w₀ = 0` (the model with `M = 1`); the two assertions
are the two conjuncts, the second under `μ₂ = E t₁² < ∞`.

**Formalization Note** `σ > 0` and `γ > 0` are implicit (the paper divides by `σ` and `√γ`).
`Δ_n(w_t − κ₁μ₁⁻¹t) = y_n − (κ₁/μ₁) t_n`, so `γ = var(y₁ − (κ₁/μ₁) t₁)`. `n_t` is `count`.
`Φ = cdf (gaussianReal 0 1)`, and each limit is asserted for every real `α`. -/
theorem corollary_9_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P)
    (hvar2 : Integrable (fun ω => varIncr w τ 1 ω ^ 2) P)
    (σ : ℝ) (hσ_pos : 0 < σ)
    (hσ : σ ^ 2 = (∫ ω, incr w τ 1 ω ^ 2 ∂P) - (∫ ω, incr w τ 1 ω ∂P) ^ 2) :
    (∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | (w t ω - (∫ ω', incr w τ 1 ω' ∂P) * (count τ t ω : ℝ)) /
          (σ * Real.sqrt (t / mu1 P τ)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α))) ∧
    (Integrable (fun ω => τ 1 ω ^ 2) P →
      ∀ γ : ℝ, 0 < γ →
        γ = variance (fun ω => incr w τ 1 ω - (∫ ω', incr w τ 1 ω' ∂P) / mu1 P τ * τ 1 ω) P →
        ∀ α : ℝ, Tendsto
          (fun t : ℝ => P.real {ω | (w t ω - (∫ ω', incr w τ 1 ω' ∂P) / mu1 P τ * t) /
              Real.sqrt (γ * t / mu1 P τ) ≤ α})
          atTop (𝓝 (cdf (gaussianReal 0 1) α))) := by sorry

end SmithRegenerative.CLT
