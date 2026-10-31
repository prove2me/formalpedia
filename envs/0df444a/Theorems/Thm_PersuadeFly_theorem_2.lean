-- Prove2me | Theorems.Thm_PersuadeFly_theorem_2
-- name    : PersuadeFly.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:32:42.939615+00:00
-- url     : https://prove2.me/theorems/91662da0-736a-4844-ab08-5e7e43b5ed5e
-- title:
--   Theorem 2, p.27 — Rai has regret $O\big(\frac{\sqrt{|\Omega|}}{p_0^2D}\sqrt{T\log T}\big)$ with high probability
-- statement:
--   Fix $\Phi>0$. Let the instance $\mathcal I$ satisfy the regularity conditions (Assumption 1) with constants $D$ and $p_0$, let $T\ge1$, and for $t\in[T]$ let
--   $$
--   \epsilon_t=\min\Big\{\sqrt{\frac{|\Omega|}{t}}\,\big(1+\sqrt{\Phi\log T}\big),\ 2\Big\}.
--   $$
--   Then for every run of the Rai algorithm with these radii and every $\mu^*\in\mathcal B_0$:
--
--   1. with probability at least $1-T^{1-\frac{3\Phi\sqrt{|\Omega|}}{56}}-T^{-8\Phi|\Omega|}$,
--   $$
--   \mathsf{Reg}_{\mathcal I}(\mathfrak{Rai},\mu^*,T)\le2\Big(\frac{20}{p_0^2D}+1\Big)\Big(1+\sqrt{|\Omega|T}\,\big(1+2\sqrt{\Phi\log T}\big)\Big);
--   $$
--   2. in particular, there is a constant $C>0$ depending only on $\Phi$ such that, whenever $D\le2$, with probability at least the same bound,
--   $$
--   \mathsf{Reg}_{\mathcal I}(\mathfrak{Rai},\mu^*,T)\le C\,\frac{\sqrt{|\Omega|}}{p_0^2D}\,\sqrt{T\log T}.
--   $$
--
--   The regret is measured against a sender who knows $\mu^*$, and the algorithm stays robustly persuasive throughout (Theorem 1). The paper shows that the $\sqrt T$ rate cannot be improved (Theorem 3).
--
--   Differences from the source:
--   - generalization: D the largest radius in Assumption 1 → any radius D for which Assumption 1.1 holds; reason: the largest radius is admissible, so the printed statement is the instance D = largest
--   - generalization: p₀ the constant of Assumption 1.2 → any p₀ > 0 with min_ω μ(ω) ≥ p₀ on B₀; reason: the paper's p₀ is such a constant
--   - generalization: first confidence set: B₀ (Algorithm 1's box) or B₁(γ₀, ϵ₀) = Δ(Ω) (text of p.20 and the proofs) → any set C₀ with B₀ ⊆ C₀ ⊆ Δ(Ω); reason: both readings are instances of C₀
--   - reading: In particular, the regret is of order O((√Ω/(p₀²D))√(T log T)) with high probability → ∃ C > 0 depending only on Φ (chosen before the instance) with regret ≤ C (√|Ω|/(p₀²D)) √(T log T) on an event of the same probability, for D ≤ 2; reason: an O(·) sentence names no constant, and C depends only on Φ, as the order expression shows; the paper's largest D is at most 2, since a ball of radius > 2 is the whole simplex
--   - encoding: OPT(μ) = max_σ V(μ, σ) subject to σ ∈ Pers(μ) → the supremum of V(μ, ·) over Pers(μ); reason: the maximum is attained (compact nonempty polytope), so the two values coincide; p.23 writes the sup
--   - encoding: choose any maximizer; probability also over any independent randomization of the algorithm → every selection rule alg satisfying IsRai, with the path law of that rule; reason: a randomized tie-break is a mixture over seeds of deterministic rules, and the bound holds for each
--   - encoding: history h_t = ∪_{τ<t}{(τ, ω_τ, a_τ, â_τ)} → the first t pairs (ω_τ, a_τ) of the path, a function Fin t → Ω × A; reason: â_τ = a_τ under robust persuasiveness (p.19); [T] = {0, …, T−1} is Fin T
--   - encoding: a time horizon of length T → T ≥ 1; reason: nondegeneracy: [T] is nonempty
--   - encoding: √Ω, log T, T^x → √|Ω|, the natural logarithm Real.log, Real.rpow; reason: √Ω means √|Ω| (the proof of Lemma 1 has 3Φ²t|Ω|, p.34); the proofs use exp(−c log T) = T^{−c}
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Theorem 2, p.27

import Mathlib
import Definitions.Def_PersuadeFly_IsRegular
import Definitions.Def_PersuadeFly_IsRai
import Definitions.Def_PersuadeFly_raiRadius
import Definitions.Def_PersuadeFly_regret
import Definitions.Def_PersuadeFly_pathEventProb

namespace PersuadeFly

/-- **Theorem 2 (regret of Rai).** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Theorem 2, p.27: suppose the instance satisfies the regularity
condition. For `t ∈ [T]` let `ϵ_t = min{√(|Ω|/t) (1 + √(Φ log T)), 2}` with `Φ > 0`. Then for all
`μ* ∈ B₀`, with probability at least `1 − T^{1 − 3Φ√|Ω|/56} − T^{−8Φ|Ω|}`, the Rai algorithm satisfies
`Reg(Rai, μ*, T) ≤ 2 (20/(p₀² D) + 1) (1 + √(|Ω|T) (1 + 2√(Φ log T)))`.
In particular, the regret is of order `O((√|Ω|/(p₀² D)) √(T log T))` with high probability.

**Formalization Note** The O(·) sentence is the second clause: for each `Φ > 0` one constant `C`,
chosen before the instance (`∃ C` precedes the types), bounds the regret by
`C (√|Ω|/(p₀² D)) √(T log T)` on an event of the same probability, for `D ≤ 2` (the paper's largest
`D` is at most 2: a ball of radius `> 2` is the whole simplex). At `T = 1` both clauses are trivial: the
probability bound is `1 − 1 − 1 = −1`.
`D` is any admissible radius and `p₀` any lower bound (see `IsRegular`); the first set `C₀` satisfies
`B₀ ⊆ C₀ ⊆ Δ(Ω)` (see `raiSet`); `log` is natural; `T^x` is `Real.rpow`. -/
theorem theorem_2 (Φ : ℝ) (hΦ : 0 < Φ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω A : Type} [Fintype Ω] [DecidableEq Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
        (I : Instance Ω A) (D p0 : ℝ), IsRegular I D p0 →
        ∀ T : ℕ, 1 ≤ T →
        ∀ (γ0 : Ω → ℝ) (C0 : Set (Ω → ℝ)) (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ),
          IsRai I γ0 C0 (raiRadius Ω Φ T) T alg →
          ∀ μ ∈ I.B0,
            1 - (T : ℝ) ^ (1 - 3 * Φ * Real.sqrt (Fintype.card Ω) / 56)
                - (T : ℝ) ^ (-(8 * Φ * Fintype.card Ω)) ≤
              pathEventProb μ alg T {path | regret I μ T path ≤
                2 * (20 / (p0 ^ 2 * D) + 1) *
                  (1 + Real.sqrt ((Fintype.card Ω : ℝ) * T) * (1 + 2 * Real.sqrt (Φ * Real.log T)))} ∧
            (D ≤ 2 →
              1 - (T : ℝ) ^ (1 - 3 * Φ * Real.sqrt (Fintype.card Ω) / 56)
                  - (T : ℝ) ^ (-(8 * Φ * Fintype.card Ω)) ≤
                pathEventProb μ alg T {path | regret I μ T path ≤
                  C * (Real.sqrt (Fintype.card Ω) / (p0 ^ 2 * D)) * Real.sqrt (T * Real.log T)}) := by sorry

end PersuadeFly
