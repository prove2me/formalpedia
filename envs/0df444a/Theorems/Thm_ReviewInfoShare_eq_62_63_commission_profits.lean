-- Prove2me | Theorems.Thm_ReviewInfoShare_eq_62_63_commission_profits
-- name    : ReviewInfoShare.eq_62_63_commission_profits
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:39.511056+00:00
-- url     : https://prove2.me/theorems/75d79a55-9cb3-4eb3-ae79-c790e027c377
-- title:
--   (62)–(63) — commission profits (platform and manufacturer lines)
-- statement:
--   Let $0<u<1$. In every pricing equilibrium of the commission contract, for each quality $q$: with information sharing, at $\gamma=0$
--   $$
--   \bar\Pi^P_s(q)=\tfrac u4\bigl(2\tilde\pi_u(q)+\phi\sigma_\theta^2q^2\bigr),\qquad \bar\Pi^M_s(q)=\tfrac{1-u}4\bigl(2\pi_u(q)+\phi\sigma_\theta^2q^2\bigr),
--   $$
--   and at $\gamma=\infty$ each bracket gains the term $\sigma_p^2(\mu_\theta^2+\phi\sigma_\theta^2)$. Without information sharing, at $\gamma=0$
--   $$
--   \bar\Pi^P_{ns}(q)=\tfrac u4\bigl(2\tilde\pi_u(q)\bigr),\qquad \bar\Pi^M_{ns}(q)=\tfrac{1-u}4\bigl(2\pi_u(q)\bigr),
--   $$
--   and at $\gamma=\infty$ each bracket gains the term $\mu_\theta^2\sigma_p^2$. The extra terms do not depend on $q$, which is why reviews leave the commission incentive unchanged.
--
--   **Formalization Note** The consumer-surplus lines of (62), (63) are not part of this mission.
--
--   Differences from the source:
--   - generalization: ϵ_q normal; θ > 0 with θ and s_θ supported on [θ̲, θ̄]; demand positive → ε with mean 0 and variance σ_p²; μ_θ > 0; no supports; no positivity of demand; reason: only two moments are used, and the printed model satisfies these hypotheses, so the statement specializes to it
--   - generalization: π_u(q̄) < π_u(q̲), π(q̄) < π(q̲) and u ∈ (0, ū), assumed throughout the paper (p.16, p.22) → 0 < u < 1; reason: only the positive margin factor 1 − u is used, and u < ū implies u < 1, so the statement specializes to the printed setting
--   - reading: limits as γ → 0 and γ → ∞ → exact statements in the boundary models q̂₂ = q (γ = 0) and q̂₂ = q + ε (γ = ∞); reason: (2) gives q̂₂ = q at γ = 0, and σ_r² = σ_p²/γ = 0 gives s_q = Q at γ = ∞; the printed proofs reduce to these two cases
--   - reading: independence of ϵ_q from (θ, s_θ) not printed → ε independent of (θ, s_θ); reason: (37)–(39) and (61)–(63) need it
--   - reading: d₁ = α + θq − p₁ is observed before stage 2 → second-stage prices depend on the signals only, not on d₁; reason: the printed pricing rules ignore that d₁ would reveal θ
--   - reading: s_θ is an unbiased estimator of θ with variance σ_m²; θ has variance σ_θ² → E[s_θ | θ] = θ a.s. and E(s_θ − θ)² = σ_m²; θ, s_θ, ε measurable and in L²; reason: θ is the unknown parameter, so unbiasedness is conditional on θ; E(s_θ − θ)² is the unconditional form of the variance; the printed variances presuppose second moments
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, (62)–(63), p.43

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Commission

namespace ReviewInfoShare

/-- Shin–Zeevi, SSRN 3886954, (62)–(63), p.43, platform and manufacturer lines. Total commission
profits at `γ = 0` and `γ = ∞`, for every pricing equilibrium, in terms of `π_u` of (17) and `π̃_u` of
(60). -/
theorem eq_62_63_commission_profits {Ω : Type*} [MeasurableSpace Ω] (P : Params)
    (hP : P.Admissible) (S : Signals Ω) (hS : IsSignalModel P S) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
    (q : Quality) :
    (∀ σ, IsCommissionEq P S u .noReviews .s q σ →
      σ.profitPlatform P S u .noReviews .s q =
        u / 4 * (2 * P.piTilde u q + P.phi * P.σθ ^ 2 * P.qual q ^ 2) ∧
      σ.profitManufacturer P S u .noReviews .s q =
        (1 - u) / 4 * (2 * P.piU u q + P.phi * P.σθ ^ 2 * P.qual q ^ 2)) ∧
    (∀ σ, IsCommissionEq P S u .perfectReviews .s q σ →
      σ.profitPlatform P S u .perfectReviews .s q =
        u / 4 * (2 * P.piTilde u q + P.phi * P.σθ ^ 2 * P.qual q ^ 2 +
          P.σp ^ 2 * (P.μ ^ 2 + P.phi * P.σθ ^ 2)) ∧
      σ.profitManufacturer P S u .perfectReviews .s q =
        (1 - u) / 4 * (2 * P.piU u q + P.phi * P.σθ ^ 2 * P.qual q ^ 2 +
          P.σp ^ 2 * (P.μ ^ 2 + P.phi * P.σθ ^ 2))) ∧
    (∀ σ, IsCommissionEq P S u .noReviews .ns q σ →
      σ.profitPlatform P S u .noReviews .ns q = u / 4 * (2 * P.piTilde u q) ∧
      σ.profitManufacturer P S u .noReviews .ns q = (1 - u) / 4 * (2 * P.piU u q)) ∧
    (∀ σ, IsCommissionEq P S u .perfectReviews .ns q σ →
      σ.profitPlatform P S u .perfectReviews .ns q =
        u / 4 * (2 * P.piTilde u q + P.μ ^ 2 * P.σp ^ 2) ∧
      σ.profitManufacturer P S u .perfectReviews .ns q =
        (1 - u) / 4 * (2 * P.piU u q + P.μ ^ 2 * P.σp ^ 2)) := by sorry

end ReviewInfoShare
