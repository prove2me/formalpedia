-- Prove2me | Theorems.Thm_ReviewInfoShare_theorem_3_limit_cases
-- name    : ReviewInfoShare.theorem_3_limit_cases
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:24.249845+00:00
-- url     : https://prove2.me/theorems/9630da8d-16a2-4705-9b7b-2fb4cf4ec9c7
-- title:
--   Proof for Theorem 3 — under commission, information is always shared at $\gamma\in\{0,\infty\}$
-- statement:
--   Under the standing commission assumptions $\pi_u(\bar q)<\pi_u(\underline q)$ and $u\in(0,\bar u)$, in either boundary regime and for every family of pricing equilibria, information sharing can be arranged, and the equilibrium quality is high exactly when the signal is strong:
--   $$
--   q^*=\bar q\iff\phi>\bar\Phi_q .
--   $$
--   Unlike under a wholesale price contract, the outcome does not depend on the regime. This is the case to which the proof of Theorem 3 reduces.
--
--   Differences from the source:
--   - generalization: ϵ_q normal; θ > 0 with θ and s_θ supported on [θ̲, θ̄]; demand positive → ε with mean 0 and variance σ_p²; μ_θ > 0; no supports; no positivity of demand; reason: only two moments are used, and the printed model satisfies these hypotheses, so the statement specializes to it
--   - generalization: π(q̄) < π(q̲), assumed throughout the paper (p.16) → not assumed under commission; reason: the commission outcome uses π_u and ū only, so the statement specializes to the printed setting
--   - reading: limits as γ → 0 and γ → ∞ → exact statements in the boundary models q̂₂ = q (γ = 0) and q̂₂ = q + ε (γ = ∞); reason: (2) gives q̂₂ = q at γ = 0, and σ_r² = σ_p²/γ = 0 gives s_q = Q at γ = ∞; the printed proofs reduce to these two cases
--   - reading: independence of ϵ_q from (θ, s_θ) not printed → ε independent of (θ, s_θ); reason: (37)–(39) and (61)–(63) need it
--   - reading: d₁ = α + θq − p₁ is observed before stage 2 → second-stage prices depend on the signals only, not on d₁; reason: the printed pricing rules ignore that d₁ would reveal θ
--   - reading: "i* = s if and only if Δᵢ Πᵐ > ρ", with ρ a decision of the platform → i* = s iff some ρ ≥ 0 has ρ < ΔᵢΠᴹ and Πᴾ_ns(q_ns) < Πᴾ_s(q_s) + ρ, with ΔᵢΠ gross of ρ; reason: p.18: sharing needs both firms better off; p.19: the paper does not optimize within the range of fees; (48) and (53) are net of ρ
--   - reading: s_θ is an unbiased estimator of θ with variance σ_m²; θ has variance σ_θ² → E[s_θ | θ] = θ a.s. and E(s_θ − θ)² = σ_m²; θ, s_θ, ε measurable and in L²; reason: θ is the unknown parameter, so unbiasedness is conditional on θ; E(s_θ − θ)² is the unconditional form of the variance; the printed variances presuppose second moments
--   - encoding: ū of (17), with no sign conditions → (α + µ_θ q̲)² < (α + µ_θ q̄)² and c̲² ≤ c̄²; reason: (17) needs a nonnegative radicand over a nonzero denominator; both conditions follow from 0 < α and 0 ≤ c̲, and the only cases they exclude where (17) is defined have c̲ < 0, which is not a unit cost
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, Proof for Theorem 3, pp.44–45

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Thresholds
import Definitions.Def_ReviewInfoShare_FeeGame
import Definitions.Def_ReviewInfoShare_Commission

namespace ReviewInfoShare

/-- Shin–Zeevi, SSRN 3886954, proof for Theorem 3, pp.44–45: under a commission contract, in each
boundary regime, information sharing can be arranged, and the equilibrium quality is high iff
`φ > Φ̄_q`. -/
theorem theorem_3_limit_cases {Ω : Type*} [MeasurableSpace Ω] (P : Params) (hP : P.Admissible)
    (S : Signals Ω) (hS : IsSignalModel P S) (u : ℝ) (hu : CommissionAssumptions P u) (r : Regime)
    (σ : Info → Quality → CommissionProfile) (hσ : IsCommissionFamily P S u r σ) :
    (commissionTable P S u r σ).Arranged ∧
    ((commissionTable P S u r σ).qStar = .high ↔ P.phiBarQ u < P.phi) := by sorry

end ReviewInfoShare
