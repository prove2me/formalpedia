-- Prove2me | Theorems.Thm_ReviewInfoShare_commission_prices
-- name    : ReviewInfoShare.commission_prices
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:31.138874+00:00
-- url     : https://prove2.me/theorems/81d8eafe-8bc5-4a2b-bb1f-c6ee09e4f503
-- title:
--   §4.1 and (64) — commission prices at $\gamma\in\{0,\infty\}$
-- statement:
--   Let $0<u<1$. For each quality $q$ the second-stage price exists and is unique: for every estimate $t$ and belief $z$,
--   $$
--   p_2^*=\tfrac12\Bigl(\alpha+tz+\frac{c_q}{1-u}\Bigr),
--   $$
--   with $t=\tilde\theta$ and $z=\hat q_2$ on the path. In either boundary regime, for each arrangement, a pricing equilibrium exists and in every pricing equilibrium
--   $$
--   p_1^*=\tfrac12\Bigl(\alpha+\mu_\theta q+\frac{c_q}{1-u}\Bigr).
--   $$
--   These are the prices that the commission profit formulas (62), (63) rest on.
--
--   Differences from the source:
--   - generalization: ϵ_q normal; θ > 0 with θ and s_θ supported on [θ̲, θ̄]; demand positive → ε with mean 0 and variance σ_p²; μ_θ > 0; no supports; no positivity of demand; reason: only two moments are used, and the printed model satisfies these hypotheses, so the statement specializes to it
--   - generalization: π_u(q̄) < π_u(q̲), π(q̄) < π(q̲) and u ∈ (0, ū), assumed throughout the paper (p.16, p.22) → 0 < u < 1; reason: only the positive margin factor 1 − u is used, and u < ū implies u < 1, so the statement specializes to the printed setting
--   - reading: limits as γ → 0 and γ → ∞ → exact statements in the boundary models q̂₂ = q (γ = 0) and q̂₂ = q + ε (γ = ∞); reason: (2) gives q̂₂ = q at γ = 0, and σ_r² = σ_p²/γ = 0 gives s_q = Q at γ = ∞; the printed proofs reduce to these two cases
--   - reading: c₁ in (64) → c_q; reason: (64) is the limit of the price on p.22, which prints c_q
--   - reading: independence of ϵ_q from (θ, s_θ) not printed → ε independent of (θ, s_θ); reason: (37)–(39) and (61)–(63) need it
--   - reading: d₁ = α + θq − p₁ is observed before stage 2 → second-stage prices depend on the signals only, not on d₁; reason: the printed pricing rules ignore that d₁ would reveal θ
--   - reading: s_θ is an unbiased estimator of θ with variance σ_m²; θ has variance σ_θ² → E[s_θ | θ] = θ a.s. and E(s_θ − θ)² = σ_m²; θ, s_θ, ε measurable and in L²; reason: θ is the unknown parameter, so unbiasedness is conditional on θ; E(s_θ − θ)² is the unconditional form of the variance; the printed variances presuppose second moments
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, §4.1, p.22; (64), p.43

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Commission

namespace ReviewInfoShare

/-- Shin–Zeevi, SSRN 3886954, §4.1, p.22, and (64), p.43: the commission prices. For `0 < u < 1` the
second-stage price exists and is unique, `p₂* = (α + θ̃q̂₂ + c_q/(1 − u))/2`, and in both boundary
regimes the pricing equilibrium exists with `p₁* = (α + µ_θ q + c_q/(1 − u))/2`.

**Formalization Note.** Stated pointwise in the estimate `t` (`= θ̃`) and belief `z` (`= q̂₂`). (64)
prints `c₁` for `c_q`, and is a limit as `γ → 0` or `γ → ∞`; at the boundary regimes it is exact. -/
theorem commission_prices {Ω : Type*} [MeasurableSpace Ω] (P : Params) (hP : P.Admissible)
    (S : Signals Ω) (hS : IsSignalModel P S) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) (q : Quality) :
    ((∃ p₂, IsCommissionStage2Eq P u q p₂) ∧
      ∀ p₂, IsCommissionStage2Eq P u q p₂ → ∀ t z : ℝ,
        p₂ t z = (P.α + t * z + P.cost q / (1 - u)) / 2) ∧
    ∀ (r : Regime) (i : Info),
      (∃ σ, IsCommissionEq P S u r i q σ) ∧
      ∀ σ, IsCommissionEq P S u r i q σ →
        σ.p₁ = (P.α + P.μ * P.qual q + P.cost q / (1 - u)) / 2 := by sorry

end ReviewInfoShare
