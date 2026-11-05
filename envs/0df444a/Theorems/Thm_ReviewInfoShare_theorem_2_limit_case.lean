-- Prove2me | Theorems.Thm_ReviewInfoShare_theorem_2_limit_case
-- name    : ReviewInfoShare.theorem_2_limit_case
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:50.864622+00:00
-- url     : https://prove2.me/theorems/3dc8e564-b96a-45ab-badf-5bb61129a029
-- title:
--   Proof for Theorem 2 — threshold strategy at $\gamma=\infty$
-- statement:
--   Assume $\pi(\bar q)<\pi(\underline q)$. At $\gamma=\infty$, for every family of pricing equilibria: if
--   $$
--   \bar q^2-\underline q^2>\Psi^\infty_i\quad\text{and}\quad\phi>\Phi^\infty_i,
--   $$
--   then information sharing can be arranged and the equilibrium quality is $\bar q$; otherwise sharing cannot be arranged and the equilibrium quality is $\underline q$. This is the threshold strategy of Definition 1 with the thresholds (14), and it is the case to which the proof of Theorem 2 reduces.
--
--   **Formalization Note** The thresholds are those of (14). The proof's (54) prints $3\sigma_p^2$ where $\sigma_p^2$ is correct.
--
--   Differences from the source:
--   - generalization: ϵ_q normal; θ > 0 with θ and s_θ supported on [θ̲, θ̄]; demand positive → ε with mean 0 and variance σ_p²; μ_θ > 0; no supports; no positivity of demand; reason: only two moments are used, and the printed model satisfies these hypotheses, so the statement specializes to it
--   - reading: limits as γ → 0 and γ → ∞ → exact statements in the boundary models q̂₂ = q (γ = 0) and q̂₂ = q + ε (γ = ∞); reason: (2) gives q̂₂ = q at γ = 0, and σ_r² = σ_p²/γ = 0 gives s_q = Q at γ = ∞; the printed proofs reduce to these two cases
--   - reading: plain c in (5) and on p.14 → c_q; reason: a plain c is neither cost symbol, and the second-stage profit on p.14 uses c_q
--   - reading: without sharing, w₂* = arg max (w − c)(α + µ_θ q̂₂ − p₂(w)) with p₂(w) containing θ̂ → p₂(w) evaluated at µ_θ in place of θ̂; reason: the manufacturer does not observe θ̂, and this reading gives (5)
--   - reading: independence of ϵ_q from (θ, s_θ) not printed → ε independent of (θ, s_θ); reason: (37)–(39) and (61)–(63) need it
--   - reading: d₁ = α + θq − p₁ is observed before stage 2 → second-stage prices depend on the signals only, not on d₁; reason: the printed pricing rules ignore that d₁ would reveal θ
--   - reading: "i* = s if and only if Δᵢ Πᵐ > ρ", with ρ a decision of the platform → i* = s iff some ρ ≥ 0 has ρ < ΔᵢΠᴹ and Πᴾ_ns(q_ns) < Πᴾ_s(q_s) + ρ, with ΔᵢΠ gross of ρ; reason: p.18: sharing needs both firms better off; p.19: the paper does not optimize within the range of fees; (48) and (53) are net of ρ
--   - reading: s_θ is an unbiased estimator of θ with variance σ_m²; θ has variance σ_θ² → E[s_θ | θ] = θ a.s. and E(s_θ − θ)² = σ_m²; θ, s_θ, ε measurable and in L²; reason: θ is the unknown parameter, so unbiasedness is conditional on θ; E(s_θ − θ)² is the unconditional form of the variance; the printed variances presuppose second moments
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, Proof for Theorem 2, p.42; Definition 1, p.19; (14), p.20

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Thresholds
import Definitions.Def_ReviewInfoShare_FeeGame
import Definitions.Def_ReviewInfoShare_Wholesale

namespace ReviewInfoShare

/-- Shin–Zeevi, SSRN 3886954, proof for Theorem 2, p.42: the threshold strategy (Definition 1, p.19)
at `γ = ∞` with `(Φ^∞ᵢ, Ψ^∞ᵢ)` of (14). If `q̄² − q̲² > Ψ^∞ᵢ` and `φ > Φ^∞ᵢ`, sharing can be arranged
and the equilibrium quality is high; otherwise sharing cannot be arranged and the equilibrium
quality is low.

**Formalization Note.** The thresholds are those of (14), not of the proof's (54), which prints
`3σ_p²` for `σ_p²`. -/
theorem theorem_2_limit_case {Ω : Type*} [MeasurableSpace Ω] (P : Params) (hP : P.Admissible)
    (S : Signals Ω) (hS : IsSignalModel P S) (hπ : P.pi .high < P.pi .low)
    (σ : Info → Quality → WholesaleProfile) (hσ : IsWholesaleFamily P S .perfectReviews σ) :
    (P.psiIInf < P.qH ^ 2 - P.qL ^ 2 ∧ P.phiIInf < P.phi →
      (wholesaleTable P S .perfectReviews σ).Arranged ∧
      (wholesaleTable P S .perfectReviews σ).qStar = .high) ∧
    (¬ (P.psiIInf < P.qH ^ 2 - P.qL ^ 2 ∧ P.phiIInf < P.phi) →
      ¬ (wholesaleTable P S .perfectReviews σ).Arranged ∧
      (wholesaleTable P S .perfectReviews σ).qStar = .low) := by sorry

end ReviewInfoShare
