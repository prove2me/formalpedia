-- Prove2me | Theorems.Thm_ReviewInfoShare_eq_39_profits_no_sharing
-- name    : ReviewInfoShare.eq_39_profits_no_sharing
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:33.293195+00:00
-- url     : https://prove2.me/theorems/9d3be477-7a89-45d7-955f-fde630a7fd78
-- title:
--   (39) — total profits without information sharing (platform and manufacturer lines)
-- statement:
--   In every pricing equilibrium without information sharing, for each quality $q$, at $\gamma=0$
--   $$
--   \Pi^P_{ns}(q)=\tfrac1{16}\bigl(2\pi(q)+4\phi\sigma_\theta^2q^2\bigr),\qquad \Pi^M_{ns}(q)=\tfrac14\pi(q),
--   $$
--   and at $\gamma=\infty$
--   $$
--   \Pi^P_{ns}(q)=\tfrac1{16}\bigl(2\pi(q)+4\phi\sigma_\theta^2q^2+\sigma_p^2(\mu_\theta^2+4\phi\sigma_\theta^2)\bigr),\qquad \Pi^M_{ns}(q)=\tfrac18\bigl(2\pi(q)+\sigma_p^2\mu_\theta^2\bigr).
--   $$
--   The manufacturer's profit does not depend on $\phi$: without sharing only the platform benefits from the signal.
--
--   **Formalization Note** The third line of (39), consumer surplus, is not part of this mission.
--
--   Differences from the source:
--   - generalization: ϵ_q normal; θ > 0 with θ and s_θ supported on [θ̲, θ̄]; demand positive → ε with mean 0 and variance σ_p²; μ_θ > 0; no supports; no positivity of demand; reason: only two moments are used, and the printed model satisfies these hypotheses, so the statement specializes to it
--   - generalization: π(q̄) < π(q̲), assumed throughout the paper (p.16) → not assumed; reason: the profits hold for each q whatever the order of π, so the statement specializes to the printed setting
--   - reading: limits as γ → 0 and γ → ∞ → exact statements in the boundary models q̂₂ = q (γ = 0) and q̂₂ = q + ε (γ = ∞); reason: (2) gives q̂₂ = q at γ = 0, and σ_r² = σ_p²/γ = 0 gives s_q = Q at γ = ∞; the printed proofs reduce to these two cases
--   - reading: plain c in (5) and on p.14 → c_q; reason: a plain c is neither cost symbol, and the second-stage profit on p.14 uses c_q
--   - reading: without sharing, w₂* = arg max (w − c)(α + µ_θ q̂₂ − p₂(w)) with p₂(w) containing θ̂ → p₂(w) evaluated at µ_θ in place of θ̂; reason: the manufacturer does not observe θ̂, and this reading gives (5)
--   - reading: independence of ϵ_q from (θ, s_θ) not printed → ε independent of (θ, s_θ); reason: (37)–(39) and (61)–(63) need it
--   - reading: d₁ = α + θq − p₁ is observed before stage 2 → second-stage prices depend on the signals only, not on d₁; reason: the printed pricing rules ignore that d₁ would reveal θ
--   - reading: s_θ is an unbiased estimator of θ with variance σ_m²; θ has variance σ_θ² → E[s_θ | θ] = θ a.s. and E(s_θ − θ)² = σ_m²; θ, s_θ, ε measurable and in L²; reason: θ is the unknown parameter, so unbiasedness is conditional on θ; E(s_θ − θ)² is the unconditional form of the variance; the printed variances presuppose second moments
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, (39), p.39

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Wholesale

namespace ReviewInfoShare

/-- Shin–Zeevi, SSRN 3886954, (39), p.39, platform and manufacturer lines. Total profits without
sharing, at `γ = 0` and `γ = ∞`, for every pricing equilibrium:
`Πᴾ_ns = (1/16)(2π(q) + 4φσ_θ²q²)` and `Πᴹ_ns = (1/4)π(q)` at `γ = 0`;
`Πᴾ_ns = (1/16)(2π(q) + 4φσ_θ²q² + σ_p²(µ_θ² + 4φσ_θ²))` and `Πᴹ_ns = (1/8)(2π(q) + σ_p²µ_θ²)`
at `γ = ∞`. -/
theorem eq_39_profits_no_sharing {Ω : Type*} [MeasurableSpace Ω] (P : Params) (hP : P.Admissible)
    (S : Signals Ω) (hS : IsSignalModel P S) (q : Quality) :
    (∀ σ, IsWholesaleEq P S .noReviews .ns q σ →
      σ.profitPlatform P S .noReviews .ns q =
        1 / 16 * (2 * P.pi q + 4 * P.phi * P.σθ ^ 2 * P.qual q ^ 2) ∧
      σ.profitManufacturer P S .noReviews .ns q = 1 / 4 * P.pi q) ∧
    (∀ σ, IsWholesaleEq P S .perfectReviews .ns q σ →
      σ.profitPlatform P S .perfectReviews .ns q =
        1 / 16 * (2 * P.pi q + 4 * P.phi * P.σθ ^ 2 * P.qual q ^ 2 +
          P.σp ^ 2 * (P.μ ^ 2 + 4 * P.phi * P.σθ ^ 2)) ∧
      σ.profitManufacturer P S .perfectReviews .ns q =
        1 / 8 * (2 * P.pi q + P.σp ^ 2 * P.μ ^ 2)) := by sorry

end ReviewInfoShare
