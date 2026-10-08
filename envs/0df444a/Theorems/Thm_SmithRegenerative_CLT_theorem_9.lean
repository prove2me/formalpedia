-- Prove2me | Theorems.Thm_SmithRegenerative_CLT_theorem_9
-- name    : SmithRegenerative.CLT.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:23.409229+00:00
-- url     : https://prove2.me/theorems/d801771b-3450-4d40-acd0-af95465a8884
-- title:
--   Theorem 9 — a centred cumulative process satisfies P{w_t/(σ(t/μ₁)^{1/2}) ≤ α} → Φ(α)
-- statement:
--   Let $w_t$ be a cumulative process on a renewal process $t_1, t_2, \dots$ with $t_0 = 0$ and $w_0 = 0$, with cycle increments $y_n = \Delta_n w_t$ and variation increments $\tilde y_n = \Delta_n \tilde w_t$. Suppose that
--   $$E(\Delta_n \tilde w_t)^2 < \infty, \qquad E \Delta_n w_t = 0, \qquad \operatorname{var} \Delta_n w_t = \sigma^2, \quad \sigma > 0,$$
--   and that $\mu_1 = E t_1 < \infty$. Then for every real $\alpha$
--   $$\lim_{t \to \infty} P\left\{ \frac{w_t}{\sigma (t/\mu_1)^{1/2}} \le \alpha \right\} = \Phi(\alpha),$$
--   where $\Phi$ is the standard normal distribution function.
--
--   This is the central limit theorem for a single cumulative process whose increments over a regeneration cycle have mean zero; Corollary 9·1 removes the centring.
--
--   **Formalization Note** $\sigma > 0$ is implicit in the paper, which divides by $\sigma$. The single process is the model with $M = 1$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 29, Theorem 9

import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), Theorem 9, p. 29: "If `E(Δ_n w̃_t)² < ∞`, `EΔ_n w_t = 0` and
`var Δ_n w_t = σ² < ∞`, then provided `μ₁ < ∞`, `lim_{t=∞} P{w_t/(σ(t/μ₁)^{1/2}) ≤ α} = Φ(α)`."

For a cumulative process with `t₀ = 0`, `w₀ = 0` (the model with `M = 1`).

**Formalization Note** `σ > 0` is implicit (the paper divides by `σ`); `σ` is the positive root
of `var y₁`. `E(Δ_n w̃)² < ∞` is integrability of `ỹ₁²`, which also makes `y₁` square
integrable, so `EΔ_n w_t` and `var Δ_n w_t` are genuine. `(t/μ₁)^{1/2}` is `Real.sqrt (t / μ₁)`.
`Φ = cdf (gaussianReal 0 1)`, and the limit is asserted for every real `α`. -/
theorem theorem_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P)
    (hvar2 : Integrable (fun ω => varIncr w τ 1 ω ^ 2) P)
    (hmean : ∫ ω, incr w τ 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hσ : variance (incr w τ 1) P = σ ^ 2) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | w t ω / (σ * Real.sqrt (t / mu1 P τ)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by sorry

end SmithRegenerative.CLT
