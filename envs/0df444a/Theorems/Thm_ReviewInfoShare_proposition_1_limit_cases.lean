-- Prove2me | Theorems.Thm_ReviewInfoShare_proposition_1_limit_cases
-- name    : ReviewInfoShare.proposition_1_limit_cases
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:44.284523+00:00
-- url     : https://prove2.me/theorems/82718900-6909-4105-82ec-5d1f0d446925
-- title:
--   Proof for Proposition 1 — wholesale quality decision at $\gamma\in\{0,\infty\}$
-- statement:
--   Assume $\pi(\bar q)<\pi(\underline q)$. In either boundary regime, for every family of pricing equilibria, the manufacturer produces low quality without information sharing, $q_{ns}=\underline q$, and with information sharing it produces high quality exactly when the signal is strong:
--   $$
--   q_s=\bar q\iff\phi>\Phi_q .
--   $$
--   The threshold $\Phi_q$ of (10) is the same in both regimes, so reviews have no direct effect on the quality decision for a fixed arrangement. This is the step to which the proof of Proposition 1 reduces, not Proposition 1 itself.
--
--   Differences from the source:
--   - generalization: ϵ_q normal; θ > 0 with θ and s_θ supported on [θ̲, θ̄]; demand positive → ε with mean 0 and variance σ_p²; μ_θ > 0; no supports; no positivity of demand; reason: only two moments are used, and the printed model satisfies these hypotheses, so the statement specializes to it
--   - reading: limits as γ → 0 and γ → ∞ → exact statements in the boundary models q̂₂ = q (γ = 0) and q̂₂ = q + ε (γ = ∞); reason: (2) gives q̂₂ = q at γ = 0, and σ_r² = σ_p²/γ = 0 gives s_q = Q at γ = ∞; the printed proofs reduce to these two cases
--   - reading: plain c in (5) and on p.14 → c_q; reason: a plain c is neither cost symbol, and the second-stage profit on p.14 uses c_q
--   - reading: without sharing, w₂* = arg max (w − c)(α + µ_θ q̂₂ − p₂(w)) with p₂(w) containing θ̂ → p₂(w) evaluated at µ_θ in place of θ̂; reason: the manufacturer does not observe θ̂, and this reading gives (5)
--   - reading: independence of ϵ_q from (θ, s_θ) not printed → ε independent of (θ, s_θ); reason: (37)–(39) and (61)–(63) need it
--   - reading: d₁ = α + θq − p₁ is observed before stage 2 → second-stage prices depend on the signals only, not on d₁; reason: the printed pricing rules ignore that d₁ would reveal θ
--   - reading: s_θ is an unbiased estimator of θ with variance σ_m²; θ has variance σ_θ² → E[s_θ | θ] = θ a.s. and E(s_θ − θ)² = σ_m²; θ, s_θ, ε measurable and in L²; reason: θ is the unknown parameter, so unbiasedness is conditional on θ; E(s_θ − θ)² is the unconditional form of the variance; the printed variances presuppose second moments
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, Proof for Proposition 1, p.40

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Thresholds
import Definitions.Def_ReviewInfoShare_FeeGame
import Definitions.Def_ReviewInfoShare_Wholesale

namespace ReviewInfoShare

/-- Shin–Zeevi, SSRN 3886954, proof for Proposition 1, p.40: the quality decision in the limit cases.
In each boundary regime, under `π(q̄) < π(q̲)`, the manufacturer produces low quality without sharing,
and with sharing it produces high quality iff `φ > Φ_q`. This is the step Proposition 1 reduces to,
not Proposition 1 itself. -/
theorem proposition_1_limit_cases {Ω : Type*} [MeasurableSpace Ω] (P : Params) (hP : P.Admissible)
    (S : Signals Ω) (hS : IsSignalModel P S) (hπ : P.pi .high < P.pi .low) (r : Regime)
    (σ : Info → Quality → WholesaleProfile) (hσ : IsWholesaleFamily P S r σ) :
    (wholesaleTable P S r σ).quality .ns = .low ∧
    ((wholesaleTable P S r σ).quality .s = .high ↔ P.phiQ < P.phi) := by sorry

end ReviewInfoShare
