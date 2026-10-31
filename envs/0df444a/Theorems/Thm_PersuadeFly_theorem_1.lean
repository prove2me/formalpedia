-- Prove2me | Theorems.Thm_PersuadeFly_theorem_1
-- name    : PersuadeFly.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:33:00.6055+00:00
-- url     : https://prove2.me/theorems/64c68bac-0b01-46dc-be4d-ef4baf79d019
-- title:
--   Theorem 1, p.22 — Rai is $\beta$-robustly persuasive with $\beta\le T^{1-3\Phi\sqrt{|\Omega|}/56}$
-- statement:
--   Let $\Phi>0$, $T\ge1$, and for $t\in[T]$ let
--   $$
--   \epsilon_t=\min\Big\{\sqrt{\frac{|\Omega|}{t}}\,\big(1+\sqrt{\Phi\log T}\big),\ 2\Big\}.
--   $$
--   Then every run of the Rai algorithm with these radii is $\beta$-robustly persuasive with
--   $$
--   \beta=\sup_{\mu^*\in\mathcal B_0}\mathbf P_{\mu^*}\Big(\bigcap_{t\in[T]}\mathcal B_t\not\ni\mu^*\Big)\le T^{\,1-\frac{3\Phi\sqrt{|\Omega|}}{56}} .
--   $$
--   In particular, for $\Phi>20$, $\beta\le T^{-0.5}$.
--
--   The confidence sets of Rai miss the true distribution with a probability that vanishes polynomially in the horizon, so receivers can trust the recommendations. No regularity condition is needed.
--
--   Differences from the source:
--   - generalization: first confidence set: B₀ (Algorithm 1's box) or B₁(γ₀, ϵ₀) = Δ(Ω) (text of p.20 and the proofs) → any set C₀ with B₀ ⊆ C₀ ⊆ Δ(Ω); reason: both readings are instances of C₀
--   - reading: coverage P_{μ*}(∩_t C_t ∋ μ*) ≥ 1 − β for the true μ* → coverage for every μ* ∈ B₀; reason: μ* is unknown; Theorem 1 takes the sup over B₀ and the proof of Theorem 3 (p.41) reads it "for all μ ∈ B₀"
--   - encoding: choose any maximizer; probability also over any independent randomization of the algorithm → every selection rule alg satisfying IsRai, with the path law of that rule; reason: a randomized tie-break is a mixture over seeds of deterministic rules, and the bound holds for each
--   - encoding: history h_t = ∪_{τ<t}{(τ, ω_τ, a_τ, â_τ)} → the first t pairs (ω_τ, a_τ) of the path, a function Fin t → Ω × A; reason: â_τ = a_τ under robust persuasiveness (p.19); [T] = {0, …, T−1} is Fin T
--   - encoding: a time horizon of length T → T ≥ 1; reason: nondegeneracy: [T] is nonempty
--   - encoding: √Ω, log T, T^x → √|Ω|, the natural logarithm Real.log, Real.rpow; reason: √Ω means √|Ω| (the proof of Lemma 1 has 3Φ²t|Ω|, p.34); the proofs use exp(−c log T) = T^{−c}
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Theorem 1, p.22

import Mathlib
import Definitions.Def_PersuadeFly_IsRai
import Definitions.Def_PersuadeFly_raiRadius
import Definitions.Def_PersuadeFly_raiBeta
import Definitions.Def_PersuadeFly_IsRobustlyPersuasive

namespace PersuadeFly

/-- **Theorem 1 (Rai is robustly persuasive).** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Theorem 1, p.22: for each `t ∈ [T]` let
`ϵ_t = min{√(|Ω|/t) (1 + √(Φ log T)), 2}` with `Φ > 0`. Then the Rai algorithm is β-robustly persuasive
with `β = sup_{μ* ∈ B₀} P_{μ*}(∩_{t ∈ [T]} B_t ∌ μ*) ≤ T^{1 − 3Φ√|Ω|/56}`. In particular, for `Φ > 20`,
`β ≤ T^{−0.5}`.

**Formalization Note** Regularity (Assumption 1) is not assumed: §3 precedes it. The first set is `C₀`
with `B₀ ⊆ C₀ ⊆ Δ(Ω)` (see `raiSet`). "Choose any" is `∀ alg` with `IsRai`. `T ≥ 1` is the horizon. -/
theorem theorem_1 {Ω A : Type} [Fintype Ω] [DecidableEq Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
    (I : Instance Ω A) (Φ : ℝ) (hΦ : 0 < Φ) (T : ℕ) (hT : 1 ≤ T)
    (γ0 : Ω → ℝ) (C0 : Set (Ω → ℝ)) (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ)
    (hRai : IsRai I γ0 C0 (raiRadius Ω Φ T) T alg) :
    IsRobustlyPersuasive I T alg (raiBeta I γ0 C0 (raiRadius Ω Φ T) T alg) ∧
      raiBeta I γ0 C0 (raiRadius Ω Φ T) T alg ≤
        (T : ℝ) ^ (1 - 3 * Φ * Real.sqrt (Fintype.card Ω) / 56) ∧
      (20 < Φ → raiBeta I γ0 C0 (raiRadius Ω Φ T) T alg ≤ (T : ℝ) ^ (-0.5 : ℝ)) := by sorry

end PersuadeFly
