-- Prove2me | Theorems.Thm_PricingStars_explicit_inference
-- name    : PricingStars.explicit_inference
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:15.02009+00:00
-- url     : https://prove2.me/theorems/4a3051bf-c3dd-41b6-b9ad-b38d11a6a478
-- title:
--   §2.1 Explicit Inference, (5)–(7) — the unique consumer inference and demand $2(\bar\psi-p(1-\kappa))$ (corrected: $2\bar\psi$ in (5))
-- statement:
--   Fix the price internalization $\kappa$, an aggregate rating $\bar\psi$ and a price $p$. A pair $(\mu,\omega)$ satisfies the consistency and rationality conditions (CONS), (RAT) of Assumption 1 if and only if
--   $$
--   \mu=2\bar\psi-1-p(1-2\kappa),\qquad \omega=1-2\bigl(\bar\psi-p(1-\kappa)\bigr).
--   $$
--   In particular the inference $(\tilde\mu,\tilde\omega)$ exists and is unique, and demand is
--   $$
--   q(\bar\psi,p)=1-\tilde\omega(\bar\psi,p)=2\bigl(\bar\psi-p(1-\kappa)\bigr).
--   $$
--
--   This turns the consumers' fixed-point heuristic into explicit linear formulas, which every later result uses.
--
--   Differences from the source:
--   - correction: μ̃(ψ̄, p) = ψ̄ − 1 − p(1 − 2κ) (5) → μ̃(ψ̄, p) = 2ψ̄ − 1 − p(1 − 2κ); reason: at κ = 0, ψ̄ = 1, p = 0 the printed pair (μ̃, ω̃) = (0, −1) violates (RAT) since 0 + (−1) ≠ 0; the corrected pair (1, −1) solves both equations, and the paper's own (30) needs the factor 2
--   - reading: ω_e(ω*) = E[ω | ω ≥ ω*] = (1 + ω*)/2 for ω ~ U[0,1] → ω_e(ω) = (1 + ω)/2 for every real ω; reason: the paper's inference and demand (6)–(7) are affine on all of ℝ² (footnote 5: beliefs on ℝ, no boundary solutions)
-- source:
--   Stenzel–Wolf–Schmidt, Pricing for the Stars: Dynamic Pricing in the Presence of Rating Systems, CRC TR 224 DP No. 143 (Jan 2020), §2.1 Explicit Inference, (5)–(7), p.9 (PDF 11)

import Mathlib
import Definitions.Def_PricingStars_Model

namespace PricingStars

/-- §2.1 "Explicit Inference", (5)–(7) (Stenzel–Wolf–Schmidt, Pricing for the Stars, CRC TR 224
DP No. 143 (Jan 2020), p.9 (PDF 11)). For every aggregate rating `ψ̄` and price `p`, the system
(CONS), (RAT) has exactly one solution `(μ̃, ω̃)`, namely
`μ̃ = 2ψ̄ − 1 − p(1 − 2κ)` (corrected (5)) and `ω̃ = 1 − 2(ψ̄ − p(1 − κ))` (6), and demand is
`q(ψ̄, p) = 1 − ω̃ = 2(ψ̄ − p(1 − κ))` (7).

**Formalization Note** The printed (5) reads `ψ̄ − 1 − p(1 − 2κ)`; at `κ = 0, ψ̄ = 1, p = 0` that
pair `(0, −1)` violates (RAT), so the factor `2` is restored. `ω_e(ω) = (1 + ω)/2` is used for every
real `ω` (the paper's unclamped linear model). -/
theorem explicit_inference (κ ψ p μ ω : ℝ) :
    (IsInference κ ψ p μ ω ↔ μ = 2 * ψ - 1 - p * (1 - 2 * κ) ∧ ω = 1 - 2 * (ψ - p * (1 - κ))) ∧
      demand κ ψ p = 2 * (ψ - p * (1 - κ)) := by sorry

end PricingStars
