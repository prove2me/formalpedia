-- Prove2me | Theorems.Thm_PricingStars_long_run_profit
-- name    : PricingStars.long_run_profit
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:30:18.626252+00:00
-- url     : https://prove2.me/theorems/0ea63585-cbe4-453f-9e59-302fd77dc1c7
-- title:
--   Display (31) — long-run profit $\tilde\pi=\tilde p\,q(\tilde\Psi,\tilde p)$ in closed form
-- statement:
--   Let $\delta\in(0,1)$, $\kappa\in[0,1)$, $\sigma>0$ and any $\theta$, and let $\tilde\Psi$, $\tilde p$ be the closed forms (28), (29). Then the long-run profit is
--   $$
--   \tilde\pi=\tilde p\cdot q(\tilde\Psi,\tilde p)=\frac{2\bigl((1-\delta)+2\delta\sigma\bigr)\bigl(\delta\sigma+(1-\delta)(1-\kappa)\bigr)}{\bigl(4\delta\sigma+(1-\delta)(3-2\kappa)\bigr)^2}\,(\theta+1)^2 .
--   $$
--
--   This closed form is what Corollary 1(c) differentiates in $\sigma$.
--
--   Differences from the source:
--   - generalization: σ ∈ [σ̄, 1] and θ > −1 → every σ > 0 and every real θ; reason: (31) is an algebraic identity between the closed forms whose denominator is positive for δ ∈ (0,1), κ ∈ [0,1), σ > 0
-- source:
--   Stenzel–Wolf–Schmidt, Pricing for the Stars: Dynamic Pricing in the Presence of Rating Systems, CRC TR 224 DP No. 143 (Jan 2020), display (31), p.14 (PDF 16)

import Mathlib
import Definitions.Def_PricingStars_Model

namespace PricingStars

/-- Display (31) (Stenzel–Wolf–Schmidt, Pricing for the Stars, CRC TR 224 DP No. 143 (Jan 2020),
p.14 (PDF 16)). With `Ψ̃` (28) and `p̃` (29), the long-run profit is
`π̃ = p̃ · q(Ψ̃, p̃) = 2((1 − δ) + 2δσ)(δσ + (1 − δ)(1 − κ)) / (4δσ + (1 − δ)(3 − 2κ))² · (θ + 1)²`.

**Formalization Note** An identity between the closed forms, stated for every `θ` and every
`σ > 0` (the paper's `σ ∈ [σ̄, 1]`); the denominator is positive for `δ ∈ (0,1)`, `κ ∈ [0,1)`,
`σ > 0`. -/
theorem long_run_profit (θ δ κ σ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hσ : 0 < σ) :
    let Ψ := (θ + 1) * (2 * (1 - δ) * (1 - κ) + δ * σ * (3 - 2 * κ)) /
      (4 * δ * σ + (1 - δ) * (3 - 2 * κ))
    let p := (θ + 1) * ((1 - δ) + 2 * δ * σ) / (4 * δ * σ + (1 - δ) * (3 - 2 * κ))
    longRunProfit κ Ψ p = 2 * ((1 - δ) + 2 * δ * σ) * (δ * σ + (1 - δ) * (1 - κ)) /
      (4 * δ * σ + (1 - δ) * (3 - 2 * κ)) ^ 2 * (θ + 1) ^ 2 := by sorry

end PricingStars
