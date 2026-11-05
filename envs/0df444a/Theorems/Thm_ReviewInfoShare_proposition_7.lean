-- Prove2me | Theorems.Thm_ReviewInfoShare_proposition_7
-- name    : ReviewInfoShare.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:44.736116+00:00
-- url     : https://prove2.me/theorems/466a7355-8a23-465b-89bd-44de831800ca
-- title:
--   Proposition 7 (corrected: fee preamble and strictness condition): reviews weaken the quality incentive under a wholesale price contract but not under a commission contract
-- statement:
--   For every family of pricing equilibria, write $\Delta_q\Pi^M_{i^*}|_{\gamma=0}$ and $\Delta_q\Pi^M_{i^*}|_{\gamma=\infty}$ for the manufacturer's equilibrium incentive to produce high quality under the wholesale price contract, without reviews and with perfectly informative reviews, and $\Delta_q\bar\Pi^M_{i^*}$ for the same under the commission contract. Here $i^*$ is the equilibrium information arrangement in each regime.
--
--   1. Under a wholesale price contract with $\pi(\bar q)<\pi(\underline q)$,
--   $$
--   \Delta_q\Pi^M_{i^*}|_{\gamma=0}\ge\Delta_q\Pi^M_{i^*}|_{\gamma=\infty},
--   $$
--   and the inequality is strict exactly when information is shared at $\gamma=0$ and not at $\gamma=\infty$, that is, when $\bar q^2-\underline q^2>\Psi^0_i$ and $\phi>\Phi^0_i$, but not both $\bar q^2-\underline q^2>\Psi^\infty_i$ and $\phi>\Phi^\infty_i$.
--   2. Under a commission contract with $\pi_u(\bar q)<\pi_u(\underline q)$ and $u\in(0,\bar u)$,
--   $$
--   \Delta_q\bar\Pi^M_{i^*}|_{\gamma=0}=\Delta_q\bar\Pi^M_{i^*}|_{\gamma=\infty}.
--   $$
--
--   This is the paper's contrast between the two contracts: reviews discourage information sharing under a wholesale price contract, which lowers the incentive to invest in quality, and they have no such effect under a commission contract.
--
--   **Formalization Note** The thresholds $\Phi^0_i$, $\Phi^\infty_i$ occur only next to the gap condition that makes their denominators positive.
--
--   Differences from the source:
--   - correction: "Fix an information fee ρ ≥ 0" → no fixed fee; i* is the equilibrium arrangement of §3.3 in each regime; reason: false if i* is the choice at a fixed fee: with θ ∈ {1, 3}, s_θ = θ ± 1, ε = ±1 equally likely, α = 10, q̲ = 1, q̄ = 2, c̲ = 1, c̄ = 301/100, ρ = 1/5 information is bought only at γ = ∞, and (23) would read −2199/40000 ≥ 5301/40000
--   - correction: strict when φ ∈ (Φ⁰ᵢ, Φ^∞ᵢ) and/or q̄² − q̲² ∈ (Ψ⁰ᵢ, Ψ^∞ᵢ) → strict iff q̄² − q̲² > Ψ⁰ᵢ and φ > Φ⁰ᵢ and not (q̄² − q̲² > Ψ^∞ᵢ and φ > Φ^∞ᵢ); reason: the second branch alone is false: in the same model with q̄ = 5/4, c̄ = 2 the gap 9/16 lies in (1/3, 2/3), information is shared in neither regime and both sides of (23) equal −43/16
--   - generalization: "strict when" (one direction) → an iff; reason: the iff contains the corrected sufficient condition
--   - generalization: ϵ_q normal; θ > 0 with θ and s_θ supported on [θ̲, θ̄]; demand positive → ε with mean 0 and variance σ_p²; μ_θ > 0; no supports; no positivity of demand; reason: only two moments are used, and the printed model satisfies these hypotheses, so the statement specializes to it
--   - generalization: π(q̄) < π(q̲) and π_u(q̄) < π_u(q̲), u ∈ (0, ū), all assumed throughout the paper (p.16, p.22) → each on its own clause: π on (a), π_u and u on (b); reason: (a) uses only π and (b) only π_u and ū, so the statement specializes to the printed setting
--   - reading: limits as γ → 0 and γ → ∞ → exact statements in the boundary models q̂₂ = q (γ = 0) and q̂₂ = q + ε (γ = ∞); reason: (2) gives q̂₂ = q at γ = 0, and σ_r² = σ_p²/γ = 0 gives s_q = Q at γ = ∞; the printed proofs reduce to these two cases
--   - reading: plain c in (5) and on p.14 → c_q; reason: a plain c is neither cost symbol, and the second-stage profit on p.14 uses c_q
--   - reading: without sharing, w₂* = arg max (w − c)(α + µ_θ q̂₂ − p₂(w)) with p₂(w) containing θ̂ → p₂(w) evaluated at µ_θ in place of θ̂; reason: the manufacturer does not observe θ̂, and this reading gives (5)
--   - reading: independence of ϵ_q from (θ, s_θ) not printed → ε independent of (θ, s_θ); reason: (37)–(39) and (61)–(63) need it
--   - reading: d₁ = α + θq − p₁ is observed before stage 2 → second-stage prices depend on the signals only, not on d₁; reason: the printed pricing rules ignore that d₁ would reveal θ
--   - reading: "i* = s if and only if Δᵢ Πᵐ > ρ", with ρ a decision of the platform → i* = s iff some ρ ≥ 0 has ρ < ΔᵢΠᴹ and Πᴾ_ns(q_ns) < Πᴾ_s(q_s) + ρ, with ΔᵢΠ gross of ρ; reason: p.18: sharing needs both firms better off; p.19: the paper does not optimize within the range of fees; (48) and (53) are net of ρ
--   - reading: s_θ is an unbiased estimator of θ with variance σ_m²; θ has variance σ_θ² → E[s_θ | θ] = θ a.s. and E(s_θ − θ)² = σ_m²; θ, s_θ, ε measurable and in L²; reason: θ is the unknown parameter, so unbiasedness is conditional on θ; E(s_θ − θ)² is the unconditional form of the variance; the printed variances presuppose second moments
--   - encoding: ū of (17), with no sign conditions → (α + µ_θ q̲)² < (α + µ_θ q̄)² and c̲² ≤ c̄²; reason: (17) needs a nonnegative radicand over a nonzero denominator; both conditions follow from 0 < α and 0 ≤ c̲, and the only cases they exclude where (17) is defined have c̲ < 0, which is not a unit cost
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, Proposition 7, pp.27–28

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Thresholds
import Definitions.Def_ReviewInfoShare_FeeGame
import Definitions.Def_ReviewInfoShare_Wholesale
import Definitions.Def_ReviewInfoShare_Commission

namespace ReviewInfoShare

/-- Shin–Zeevi, *Product Quality and Information Sharing in the Presence of Reviews*, SSRN 3886954,
Proposition 7, pp.27–28, corrected. For every family of pricing equilibria:

(a) under a wholesale price contract with `π(q̄) < π(q̲)`, the equilibrium incentive `Δ_q Πᴹ_{i*}` at
`γ = ∞` is at most that at `γ = 0`, (23), and strictly less iff information is shared at `γ = 0` and
not at `γ = ∞`, in terms of the thresholds of (13) and (14);

(b) under a commission contract with the standing assumptions of p.22, the two incentives are
equal, (24).

**Formalization Note.** `i*` is the equilibrium arrangement of §3.3 in each regime, not the choice at
a fixed fee: the printed "Fix an information fee `ρ ≥ 0`" is false for that reading. The printed
"strict when `φ ∈ (Φ⁰ᵢ, Φ^∞ᵢ)` and/or `q̄² − q̲² ∈ (Ψ⁰ᵢ, Ψ^∞ᵢ)`" is replaced by an iff. The thresholds
`Φ⁰ᵢ`, `Φ^∞ᵢ` occur only next to the gap condition that makes their denominators positive. -/
theorem proposition_7 {Ω : Type*} [MeasurableSpace Ω] (P : Params) (hP : P.Admissible)
    (S : Signals Ω) (hS : IsSignalModel P S) :
    (P.pi .high < P.pi .low →
      ∀ σ : Regime → Info → Quality → WholesaleProfile,
        (∀ r, IsWholesaleFamily P S r (σ r)) →
        (wholesaleTable P S .perfectReviews (σ .perfectReviews)).incentive ≤
          (wholesaleTable P S .noReviews (σ .noReviews)).incentive ∧
        ((wholesaleTable P S .perfectReviews (σ .perfectReviews)).incentive <
            (wholesaleTable P S .noReviews (σ .noReviews)).incentive ↔
          (P.psiI0 < P.qH ^ 2 - P.qL ^ 2 ∧ P.phiI0 < P.phi) ∧
            ¬ (P.psiIInf < P.qH ^ 2 - P.qL ^ 2 ∧ P.phiIInf < P.phi))) ∧
    (∀ u : ℝ, CommissionAssumptions P u →
      ∀ σ : Regime → Info → Quality → CommissionProfile,
        (∀ r, IsCommissionFamily P S u r (σ r)) →
        (commissionTable P S u .noReviews (σ .noReviews)).incentive =
          (commissionTable P S u .perfectReviews (σ .perfectReviews)).incentive) := by sorry

end ReviewInfoShare
