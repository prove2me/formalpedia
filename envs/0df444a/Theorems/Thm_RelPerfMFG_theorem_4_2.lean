-- Prove2me | Theorems.Thm_RelPerfMFG_theorem_4_2
-- name    : RelPerfMFG.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:29:32.421394+00:00
-- url     : https://prove2.me/theorems/a5260e75-7835-4b7f-a2cc-667c5c1be796
-- title:
--   Theorem 4.2: the two-layer game has the equilibrium $(\beta^*,a^*)$ with $a^*$ the unique team-wise equilibrium and $\beta^*$ given by (4.6)
-- statement:
--   Work in the standing model of §3–§4: $X=(X_1,\dots,X_N)$ independent of $Y$, $X_1,\dots,X_N$ independent, $\phi_t$ jointly Borel with $\mathbb E[\phi_t(a,X_{t+1})]=a$ (3.1), costs $C_t$ strictly increasing, strictly convex, $C^1$ with $C_t(0)=C_t'(0)=0$, rewards $R,G\ge0$ jointly Borel, $\theta\in(0,1)$, $N\ge1$, and let Assumption 4.1 hold. Then there is $a^*\in\mathcal A$ such that
--
--   1. $a^*$ is a team-wise equilibrium (Definition 4.1), and every team-wise equilibrium equals $a^*$ almost surely;
--   2. $0<\mathbb E[G(\sum_ta^*_t)]<\infty$;
--   3. with
--   $$\beta^*:=\frac{R'\big(\sum_{t=0}^{N-1}a^*_t\big)\sum_{t=0}^{N-1}a^*_t}{R\big(\sum_{t=0}^{N-1}a^*_t\big)}+\frac{\theta G'\big(\sum_{t=0}^{N-1}a^*_t\big)\sum_{t=0}^{N-1}a^*_t}{\theta G\big(\sum_{t=0}^{N-1}a^*_t\big)+(1-\theta)\mathbb E\big[G\big(\sum_{t=0}^{N-1}a^*_t\big)\big]}\in\mathcal F^Y_N,\quad(4.6)$$
--   $(\beta^*,a^*)$ is an equilibrium for the two-layer mean-field contribution game (Definition 4.3): $a^*$ is an equilibrium control w.r.t. $\beta^*$ and $a''=a^*$, i.e. $\mathfrak V(a;a^*,\beta^*,a^*)\le\mathfrak V(a^*;a^*,\beta^*,a^*)$ for every $a\in\tilde{\mathcal A}$ (4.4), and $\mathfrak V(a^*;a^*,\beta^*,a^*)=\sup_{a'\in\tilde{\mathcal A}}\mathbb V(\bar a',\bar a^*)$ (4.5).
--
--   So the competition among teams is resolved by the unique team-wise equilibrium, and within each team the ratio-based criterion with the explicit weight $\beta^*$ makes every member's equilibrium payoff equal to the best team payoff; the second term of $\beta^*$ is the extra intra-team competition that inter-team competition calls for.
--
--   **Formalization Note** Representative-player and representative-team form; aggregates $\bar a'_t=\mathbb E[a'_t\mid\mathcal F^Y_t]$. Payoff comparisons, the equilibrium value and the supremum in (4.5) are taken in the extended sense. $R'$, $G'$ are derivatives in $x$.
--
--   Differences from the source:
--   - reading: "continuously differentiable" for R, G, RG, J → continuous on ℝ₊ and C¹ on (0, ∞) (footnote 2); derivative conditions at x > 0; reason: footnote 2 (p.5) defines this meaning; the paper's Examples 3.1 and 4.1 (R = x^p g(y), p < 1) satisfy its assumptions only in this sense.
--   - encoding: unique team-wise equilibrium → every team-wise equilibrium equals a* almost surely in every period; reason: controls are random variables, determined up to null sets.
--   - encoding: 0 < E[G(Σ a*_t)] < ∞ → G(Σ a*_t, Y) integrable and 0 < ∫ G(Σ a*_t, Y) dμ; reason: nonnegative integrand; a Bochner integral "< ∞" would be vacuous.
--   - encoding: a* ∈ argmax_{a∈𝒜} 𝕍(a, a*) → 𝕍(a*, a*) integrable and every a ∈ 𝒜 has 𝕍(a, a*) ≤ 𝕍(a*, a*) in the extended sense (ExpLE); reason: an argmax of expectations presupposes a finite maximal value; the extended comparison keeps every deviation.
--   - encoding: expected payoffs, argmax and sup of expectations → extended-sense comparisons E[f] ≤ v (ExpLE) and values E[f] = v (ExpEq) with E[f] = E[f⁺] − E[f⁻]; no claim where E[f⁺] = E[f⁻] = ∞; reason: the Bochner integral is 0 for non-integrable integrands; the paper's expectations are presupposed to exist, and with a general φ satisfying only (3.1) the noisy performance term need not be integrable.
--   - encoding: 𝔙(â′; â′, β, a″) = sup_{a′∈𝒜̃} 𝕍(ā′, ā″) (4.5) → IsTeamSup: every a′ ∈ 𝒜̃ has 𝕍(ā′, ā″) ≤ v in the extended sense, and for every ε > 0 some a′ with integrable team payoff has 𝕍(ā′, ā″) > v − ε; reason: a real ⨆ is junk on unbounded sets; this is the extended-real supremum.
--   - encoding: a continuum of players (teams) i ∈ [0, 1] with i.i.d. noises Xⁱ independent of Y → one representative player with noise X; population aggregates are conditional expectations given F^Y; reason: the paper writes every payoff for a representative player (F on p.13, (4.1), 𝔙 on p.19); payoffs depend only on the joint law of (Xⁱ, Y).
--   - encoding: controls in 𝒜 (resp. 𝒜̃): F^Y- (resp. F^{i,Y}-) adapted, ℝ₊-valued → families a k : Ω → ℝ, nonnegative, measurable for σ of the k-prefix of Y (resp. of X and Y); reason: Doob–Dynkin: the same as the paper's control laws a_k(X_1, …, X_k, Y_1, …, Y_k).
--   - encoding: conditional expectations E[· | F^Y_k] of nonnegative or non-integrable quantities → integrals against the regular conditional distribution (condDistrib) given the k-prefix of the common-noise path; reason: a version of the conditional expectation that exists for every outcome and for nonnegative non-integrable integrands; Mathlib's condExp of a non-integrable function is 0.
--   - encoding: an N-period model → 0 < N; reason: excludes only the degenerate model N = 0, where all sums are empty and (3.6) is vacuous.
--   - encoding: periods k = 0, …, N − 1 with noises X_{k+1}, Y_{k+1}; F^Y_k = σ(Y_1, …, Y_k) → Lean coordinates X k, Y k (0-based); F^Y_k is generated by the k-prefix of the noise path (truncPath); reason: Lean convention; same instances.
--   - encoding: Assumption 4.1(iv)–(v), inequalities between random variables 'for all x ≥ 0' (resp. all x ∈ ℝ₊ᴺ) → almost surely, simultaneously for all x (and t); reason: R, RG are continuous on ℝ₊ by (i), G = RG/R is continuous on (0, ∞) where R > 0 by (ii), and the costs are C¹, so the a.s. inequality for each x and for all x at once coincide; same instances.
--   - reading: the member payoff 𝔙 (p.19) ends with − Σ_t C(a_t) → − Σ_t C_t(a_t); reason: §4 costs are period-dependent (C_t, p.17) and (4.1) uses C_t(a_t); the unindexed C is a typo.
--   - reading: Definition 4.3: '(β*, a*) … if β is an intra-team optimal RPC w.r.t. a*' → β* is an intra-team optimal RPC w.r.t. a*; reason: the definition is about the pair (β*, a*); β is unbound there.
-- source:
--   Zhou, Optimal relative performance criteria in mean field contribution games, SSRN 3742584 (Nov. 13, 2022), Theorem 4.2, p.20, (4.6); Definitions 4.1–4.3, pp.19–20

import Mathlib
import Definitions.Def_RelPerfMFG_Setup
import Definitions.Def_RelPerfMFG_Centralized
import Definitions.Def_RelPerfMFG_TwoLayer

open MeasureTheory ProbabilityTheory

namespace RelPerfMFG

/-- **Theorem 4.2**, Zhou, *Optimal relative performance criteria in mean field contribution
games*, SSRN 3742584 (Nov. 13, 2022), p.20. Under Assumption 4.1, there exists an equilibrium
`(β*, a*)` for the two-layer mean-field contribution game, where `a*` is the unique team-wise
equilibrium given in Theorem 4.1 and `β* ∈ F^Y_N` is given by
`β* := R′(Σ_t a*_t) Σ_t a*_t / R(Σ_t a*_t)
  + θ G′(Σ_t a*_t) Σ_t a*_t / (θ G(Σ_t a*_t) + (1 − θ) E[G(Σ_t a*_t)])` (4.6).

Spelled out: there is `a* ∈ 𝒜` such that (1) `a*` is a team-wise equilibrium (Definition 4.1);
(2) every team-wise equilibrium equals `a*` a.s.; (3) `0 < E[G(Σ_t a*_t)] < ∞` (Theorem 4.1);
(4) with `β*` from (4.6), `(β*, a*)` is an equilibrium for the two-layer game (Definition 4.3):
`a*` is an equilibrium control w.r.t. `β*` and `a″ = a*` against every deviation in `𝒜̃` (4.4),
and `𝔙(a*; a*, β*, a*) = sup_{a′ ∈ 𝒜̃} 𝕍(ā′, ā*)` (4.5).

**Formalization Note.** §3–§4 standing model: `(Ω, μ)` a probability space; noises `X`, `Y`
independent; `X₁, …, X_N` independent; `φ_t` jointly Borel with (3.1); `C_t` strictly increasing,
strictly convex, `C¹`, `C_t(0) = C′_t(0) = 0`; `R, G ≥ 0` jointly Borel; `θ ∈ (0, 1)`; `N ≥ 1`.
Representative-player and representative-team form; aggregates `ā′_t = E[a′_t | F^Y_t]` are
integrals against the regular conditional distribution of `a′_t` given the first `t` common
noises (`aggregate`). The printed `C(a_t)` in `𝔙` is `C_t(a_t)`, and the printed "`β` is an
intra-team optimal RPC" in Definition 4.3 is `β*`. Payoff comparisons and the supremum of (4.5)
are in the extended sense. `β*` is the explicit random variable `betaStar` (`R′ = rderiv`).
Uniqueness is up to a.s. equality. 0-based periods. -/
theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] {N d e : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → NoisePath N d) (Y : Ω → NoisePath N e)
    (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (hmodel : IsNoiseModel μ X Y φ)
    (hXind : iIndepFun (fun k ω => X ω k) μ)
    (C : Fin N → ℝ → ℝ) (hC : IsCostS4 C)
    (R G : ℝ → NoisePath N e → ℝ) (hR : IsReward R) (hG : IsReward G)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hA : Assumption41 μ Y C R G) :
    ∃ aS : Fin N → Ω → ℝ, IsTeamwiseEq μ Y C R G θ aS ∧
      (∀ a : Fin N → Ω → ℝ, IsTeamwiseEq μ Y C R G θ a → ∀ t, a t =ᵐ[μ] aS t) ∧
      Integrable (fun ω => G (∑ t, aS t ω) (Y ω)) μ ∧
      0 < ∫ ω, G (∑ t, aS t ω) (Y ω) ∂μ ∧
      IsTwoLayerEquilibrium μ X Y φ C R G θ (betaStar μ Y R G θ aS) aS := by sorry

end RelPerfMFG
