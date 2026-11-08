-- Prove2me | Theorems.Thm_ReviewInfoShare_eq_6_first_stage_prices
-- name    : ReviewInfoShare.eq_6_first_stage_prices
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:40:52.160531+00:00
-- url     : https://prove2.me/theorems/dbaf76fe-9427-46f0-8a4d-3b350f49bf13
-- title:
--   (6) — first-stage wholesale-contract prices at $\gamma\in\{0,\infty\}$
-- statement:
--   In either boundary regime, for each arrangement $i$ and quality $q$, a pricing equilibrium exists, and in every pricing equilibrium
--   $$
--   (p_1^*,w_1^*)=(\bar p,\bar w)=\Bigl(\tfrac14(3\alpha+3\mu_\theta q+c_q),\ \tfrac12(\alpha+\mu_\theta q+c_q)\Bigr).
--   $$
--   In these regimes second-stage profits do not depend on first-stage prices, so the first stage is a static problem. This is the input to the first-stage terms of (38), (39).
--
--   Differences from the source:
--   - generalization: ϵ_q normal; θ > 0 with θ and s_θ supported on [θ̲, θ̄]; demand positive → ε with mean 0 and variance σ_p²; μ_θ > 0; no supports; no positivity of demand; reason: only two moments are used, and the printed model satisfies these hypotheses, so the statement specializes to it
--   - generalization: π(q̄) < π(q̲), assumed throughout the paper (p.16) → not assumed; reason: the first-stage prices hold for each q whatever the order of π, so the statement specializes to the printed setting
--   - reading: limits as γ → 0 and γ → ∞ → exact statements in the boundary models q̂₂ = q (γ = 0) and q̂₂ = q + ε (γ = ∞); reason: (2) gives q̂₂ = q at γ = 0, and σ_r² = σ_p²/γ = 0 gives s_q = Q at γ = ∞; the printed proofs reduce to these two cases
--   - reading: plain c in (5) and on p.14 → c_q; reason: a plain c is neither cost symbol, and the second-stage profit on p.14 uses c_q
--   - reading: without sharing, w₂* = arg max (w − c)(α + µ_θ q̂₂ − p₂(w)) with p₂(w) containing θ̂ → p₂(w) evaluated at µ_θ in place of θ̂; reason: the manufacturer does not observe θ̂, and this reading gives (5)
--   - reading: independence of ϵ_q from (θ, s_θ) not printed → ε independent of (θ, s_θ); reason: (37)–(39) and (61)–(63) need it
--   - reading: d₁ = α + θq − p₁ is observed before stage 2 → second-stage prices depend on the signals only, not on d₁; reason: the printed pricing rules ignore that d₁ would reveal θ
--   - reading: s_θ is an unbiased estimator of θ with variance σ_m²; θ has variance σ_θ² → E[s_θ | θ] = θ a.s. and E(s_θ − θ)² = σ_m²; θ, s_θ, ε measurable and in L²; reason: θ is the unknown parameter, so unbiasedness is conditional on θ; E(s_θ − θ)² is the unconditional form of the variance; the printed variances presuppose second moments
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, (6), p.14

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Wholesale

namespace ReviewInfoShare

/-- Shin–Zeevi, SSRN 3886954, (6), p.14. In both boundary regimes, for each arrangement and quality,
the pricing equilibrium exists and its first-stage prices are
`(p̄, w̄) = (¼(3α + 3µ_θ q + c_q), ½(α + µ_θ q + c_q))`.

**Formalization Note.** (6) is printed as a limit as `γ → 0` or `γ → ∞`; at the boundary regimes
second-stage profits do not depend on first-stage prices, so it is the exact price there. -/
theorem eq_6_first_stage_prices {Ω : Type*} [MeasurableSpace Ω] (P : Params) (hP : P.Admissible)
    (S : Signals Ω) (hS : IsSignalModel P S) (r : Regime) (i : Info) (q : Quality) :
    (∃ σ, IsWholesaleEq P S r i q σ) ∧
    ∀ σ, IsWholesaleEq P S r i q σ →
      σ.p₁ σ.w₁ = (3 * P.α + 3 * P.μ * P.qual q + P.cost q) / 4 ∧
      σ.w₁ = (P.α + P.μ * P.qual q + P.cost q) / 2 := by sorry

end ReviewInfoShare
