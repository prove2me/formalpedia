-- Prove2me | Theorems.Thm_PricingStars_corollary_1_derivatives
-- name    : PricingStars.corollary_1_derivatives
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:29:37.817113+00:00
-- url     : https://prove2.me/theorems/6b765b8b-74e5-4615-805c-0b2505fdae11
-- title:
--   Proof of Corollary 1, (62)–(64) — the $\sigma$-derivatives of $\tilde p$, $\tilde\pi$ and $\tilde\Psi$
-- statement:
--   Let $\delta\in(0,1)$, $\kappa\in[0,1)$ and any $\theta$, and write $D(\sigma)=(1-\delta)(3-2\kappa)+4\delta\sigma$. As functions of $\sigma$, the closed forms $\tilde p$ (29), $\tilde\pi$ (31) and $\tilde\Psi$ (28) satisfy, at every $\sigma>0$,
--   $$
--   \frac{\partial\tilde p}{\partial\sigma}=\frac{2(1-\delta)\delta(\theta+1)}{D(\sigma)^2}(1-2\kappa)\quad(62),\qquad
--   \frac{\partial\tilde\pi}{\partial\sigma}=\frac{2(1-\delta)^2\delta(\theta+1)^2}{D(\sigma)^3}(1-2\kappa)^2\quad(63),
--   $$
--   $$
--   \frac{\partial\tilde\Psi}{\partial\sigma}=\frac{(1-\delta)\delta(\theta+1)}{D(\sigma)^2}(1-2\kappa)^2\quad(64),
--   $$
--   and, when $\theta>-1$, the three factors in front of $(1-2\kappa)$ and $(1-2\kappa)^2$ are positive.
--
--   So the sign of $\partial\tilde p/\partial\sigma$ is that of $1-2\kappa$, while $\tilde\pi$ and $\tilde\Psi$ are weakly increasing, strictly for $\kappa\neq1/2$.
--
--   Differences from the source:
--   - generalization: σ ∈ [σ̄, 1] (and θ > −1 for the derivative formulas) → every σ > 0 and every real θ for (62)–(64); θ > −1 only for the positivity of the factors; reason: the derivative identities hold wherever D(σ) ≠ 0, which includes every σ > 0
-- source:
--   Stenzel–Wolf–Schmidt, Pricing for the Stars: Dynamic Pricing in the Presence of Rating Systems, CRC TR 224 DP No. 143 (Jan 2020), Proof of Corollary 1, (62)–(64), p.26 (PDF 28)

import Mathlib

namespace PricingStars

/-- Proof of Corollary 1, (62)–(64) (Stenzel–Wolf–Schmidt, Pricing for the Stars, CRC TR 224
DP No. 143 (Jan 2020), p.26 (PDF 28)). As functions of `σ`, the closed forms `p̃` (29), `π̃` (31)
and `Ψ̃` (28) have the derivatives, with `D(σ) = (1 − δ)(3 − 2κ) + 4δσ`,
`∂p̃/∂σ = 2(1 − δ)δ(θ + 1)/D² · (1 − 2κ)` (62),
`∂π̃/∂σ = 2(1 − δ)²δ(θ + 1)²/D³ · (1 − 2κ)²` (63),
`∂Ψ̃/∂σ = (1 − δ)δ(θ + 1)/D² · (1 − 2κ)²` (64),
at every `σ > 0`, for `δ ∈ (0,1)`, `κ ∈ [0,1)` and every `θ`. For `θ > −1` the three factors
in front of `(1 − 2κ)` and `(1 − 2κ)²` (overbraced "> 0" on the page) are positive.

**Formalization Note** The functions are the closed forms on all of `ℝ`; `D(σ) > 0` at `σ > 0`. -/
theorem corollary_1_derivatives (θ δ κ σ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hσ : 0 < σ) :
    HasDerivAt (fun s : ℝ => (θ + 1) * ((1 - δ) + 2 * δ * s) / (4 * δ * s + (1 - δ) * (3 - 2 * κ)))
      (2 * (1 - δ) * δ * (θ + 1) / ((1 - δ) * (3 - 2 * κ) + 4 * δ * σ) ^ 2 * (1 - 2 * κ)) σ ∧
    HasDerivAt (fun s : ℝ => 2 * ((1 - δ) + 2 * δ * s) * (δ * s + (1 - δ) * (1 - κ)) /
        (4 * δ * s + (1 - δ) * (3 - 2 * κ)) ^ 2 * (θ + 1) ^ 2)
      (2 * (1 - δ) ^ 2 * δ * (θ + 1) ^ 2 / ((1 - δ) * (3 - 2 * κ) + 4 * δ * σ) ^ 3 *
        (1 - 2 * κ) ^ 2) σ ∧
    HasDerivAt (fun s : ℝ => (θ + 1) * (2 * (1 - δ) * (1 - κ) + δ * s * (3 - 2 * κ)) /
        (4 * δ * s + (1 - δ) * (3 - 2 * κ)))
      ((1 - δ) * δ * (θ + 1) / ((1 - δ) * (3 - 2 * κ) + 4 * δ * σ) ^ 2 * (1 - 2 * κ) ^ 2) σ ∧
    (-1 < θ →
      0 < 2 * (1 - δ) * δ * (θ + 1) / ((1 - δ) * (3 - 2 * κ) + 4 * δ * σ) ^ 2 ∧
      0 < 2 * (1 - δ) ^ 2 * δ * (θ + 1) ^ 2 / ((1 - δ) * (3 - 2 * κ) + 4 * δ * σ) ^ 3 ∧
      0 < (1 - δ) * δ * (θ + 1) / ((1 - δ) * (3 - 2 * κ) + 4 * δ * σ) ^ 2) := by sorry

end PricingStars
