-- Prove2me | Theorems.Thm_ReviewInfoShare_proposition_2_limit_cases
-- name    : ReviewInfoShare.proposition_2_limit_cases
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:14.091564+00:00
-- url     : https://prove2.me/theorems/bf66b952-f9b9-43ec-9b50-de0861a16a72
-- title:
--   Proof for Proposition 2 — commission quality decision at $\gamma\in\{0,\infty\}$
-- statement:
--   Under the standing commission assumptions $\pi_u(\bar q)<\pi_u(\underline q)$ and $u\in(0,\bar u)$, in either boundary regime and for every family of pricing equilibria, the manufacturer produces low quality without information sharing, and with sharing
--   $$
--   q_s=\bar q\iff\phi>\bar\Phi_q .
--   $$
--   This is the step to which the proof of Proposition 2 reduces, not Proposition 2 itself.
--
--   Differences from the source:
--   - generalization: ϵ_q normal; θ > 0 with θ and s_θ supported on [θ̲, θ̄]; demand positive → ε with mean 0 and variance σ_p²; μ_θ > 0; no supports; no positivity of demand; reason: only two moments are used, and the printed model satisfies these hypotheses, so the statement specializes to it
--   - generalization: π(q̄) < π(q̲), assumed throughout the paper (p.16) → not assumed under commission; reason: the commission quality decision uses π_u only, so the statement specializes to the printed setting
--   - reading: limits as γ → 0 and γ → ∞ → exact statements in the boundary models q̂₂ = q (γ = 0) and q̂₂ = q + ε (γ = ∞); reason: (2) gives q̂₂ = q at γ = 0, and σ_r² = σ_p²/γ = 0 gives s_q = Q at γ = ∞; the printed proofs reduce to these two cases
--   - reading: independence of ϵ_q from (θ, s_θ) not printed → ε independent of (θ, s_θ); reason: (37)–(39) and (61)–(63) need it
--   - reading: d₁ = α + θq − p₁ is observed before stage 2 → second-stage prices depend on the signals only, not on d₁; reason: the printed pricing rules ignore that d₁ would reveal θ
--   - reading: s_θ is an unbiased estimator of θ with variance σ_m²; θ has variance σ_θ² → E[s_θ | θ] = θ a.s. and E(s_θ − θ)² = σ_m²; θ, s_θ, ε measurable and in L²; reason: θ is the unknown parameter, so unbiasedness is conditional on θ; E(s_θ − θ)² is the unconditional form of the variance; the printed variances presuppose second moments
--   - encoding: ū of (17), with no sign conditions → (α + µ_θ q̲)² < (α + µ_θ q̄)² and c̲² ≤ c̄²; reason: (17) needs a nonnegative radicand over a nonzero denominator; both conditions follow from 0 < α and 0 ≤ c̲, and the only cases they exclude where (17) is defined have c̲ < 0, which is not a unit cost
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, Proof for Proposition 2, p.44; (18), p.22

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Thresholds
import Definitions.Def_ReviewInfoShare_FeeGame
import Definitions.Def_ReviewInfoShare_Commission

namespace ReviewInfoShare

/-- Shin–Zeevi, SSRN 3886954, proof for Proposition 2, p.44: the commission quality decision in the
limit cases. In each boundary regime the manufacturer produces low quality without sharing, and with
sharing it produces high quality iff `φ > Φ̄_q` of (18). This is the step Proposition 2 reduces to,
not Proposition 2 itself. -/
theorem proposition_2_limit_cases {Ω : Type*} [MeasurableSpace Ω] (P : Params) (hP : P.Admissible)
    (S : Signals Ω) (hS : IsSignalModel P S) (u : ℝ) (hu : CommissionAssumptions P u) (r : Regime)
    (σ : Info → Quality → CommissionProfile) (hσ : IsCommissionFamily P S u r σ) :
    (commissionTable P S u r σ).quality .ns = .low ∧
    ((commissionTable P S u r σ).quality .s = .high ↔ P.phiBarQ u < P.phi) := by sorry

end ReviewInfoShare
