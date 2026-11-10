-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_lemma_4_10
-- name    : TurnstileRank.TightBounds.lemma_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:08:30.339732+00:00
-- url     : https://prove2.me/theorems/85db5650-07ab-42b8-9b92-083bfe1c5ea8
-- title:
--   Lemma 4.10 — accuracy and conditional variance (both directions)
-- statement:
--   Lemma 4.10 (Accuracy and conditional variance). For every η > 0, there exist a, δ > 0 such that P[|T − R| > a√d] ≤ δ ⇒ Var(R | X, A_ρ(V_{1:d}; N), ρ) ≤ ηd. Conversely, for every a, δ > 0, this bound with sufficiently small η > 0 ensures the same accuracy for the conditional mean.
--
--   In Lean: (forward) for every $\eta>0$ there are $a,\delta>0$ such that for every admissible base $k$, every $d$, every linear sketch with noise, every sign function $\sigma$ and every estimate $T(\rho,X,A_\rho(V_{1:d};N))$: if $P[|T-R|>a\sqrt d]\le\delta$ then $\mathrm{Var}(R\mid\rho,X,A_\rho(V_{1:d};N))\le\eta d$. (Converse) for every $a,\delta>0$ there is $\eta>0$ such that, in the same setting, $\mathrm{Var}(R\mid\rho,X,A_\rho(V_{1:d};N))\le\eta d$ implies $P[|E[R\mid\rho,X,A_\rho(V_{1:d};N)]-R|>a\sqrt d]\le\delta$. Here $R$ is the signed rank of Definition 4.4 and probabilities average over the hard instance, the public randomness and the noise.
--
--   Differences from the source:
--   - encoding: strings of [k]^d with 1-indexed digits X[1..d] and levels i = 1..d → `Str d k = Fin d → Fin k` with 0-based digit positions and item indices (paper level i is `i.val + 1`, digit X[j] is `X ⟨j − 1⟩`); reason: a bijective reindexing; `strVal` is the lexicographic order, most significant digit first
--   - encoding: random variables (public randomness, noise, hard instance) on an unspecified probability space → one discrete law (`PMF`) on the sample type `Ρ × G × HardSample d k`; probabilities by `prob`; reason: all quantities of §3.2 are sums over values, i.e. the variables are discrete; a PMF may live on an uncountable type with countable support
--   - encoding: an abelian group G_ρ that depends on the seed ρ → one abelian group G for every seed; reason: the groups G_ρ embed in the product Π_ρ G_ρ, which changes no state and no information quantity
--   - encoding: ρ independent of (X, V_{1:d}); noise N independent of (X, V_{1:d}) given ρ → (ρ, N) has an arbitrary discrete joint law `S.law`, independent of the hard instance (`NoisySketch.jointLaw`); reason: the two independence statements together say exactly that (ρ, N) is independent of (X, V_{1:d})
--   - encoding: V_i uniform among strings agreeing with X in their first i − 1 digits, independently given X → V_i copies X before position i and an independent uniform string W_i from position i on (`splice`); reason: the same joint law of (X, V_1, …, V_d)
--   - reading: fix a sufficiently large power of two k with k⁻¹ ≤ η₀/8 (§4.1) → every power of two k with k⁻¹ ≤ η₀/8 (`KeyBase k`), quantified after the absolute constants; reason: the section's proofs use only k⁻¹ ≤ η₀/8, and its constants do not depend on k; holding for every such k is the stronger reading of "fix"
--   - encoding: an estimate T of R → any function `T ρ X M` of the seed, the query and the final state; reason: the decoder sees exactly (ρ, X, A_ρ(V_{1:d}; N)) (proof of Lemma 4.10: "T̂ is determined by (X, A_ρ(V_{1:d}; N), ρ)")
--   - encoding: Var(Z | C) of Definition 4.9, with ρ suppressed from the conditioning ("Where not displayed explicitly, ρ is suppressed", p. 16) → `condVar P Z C` = the number E[(Z − E[Z | C])²], with ρ inside every conditioning variable C; reason: Definition 4.9 and the paper's convention verbatim; every Z used is bounded, so the infinite sums converge
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Lemma 4.10, printed p. 16 (PDF 17)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_HardInstance

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Lemma 4.10 (Accuracy and conditional variance), both directions. -/
theorem lemma_4_10 :
    (∀ η : ℝ, 0 < η → ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧
      ∀ (k : ℕ) [NeZero k], KeyBase k → ∀ (d : ℕ) (Ρ G : Type) [AddCommGroup G]
        (S : NoisySketch d k Ρ G) (σ : Ρ → Str d k → ℝ), IsSign σ →
        ∀ T : Ρ → Str d k → G → ℝ,
          prob S.jointLaw
              {ω | a * Real.sqrt d < |T ω.1 ω.2.2.X (S.state ω) - signedRank σ ω|} ≤ δ →
          condVar S.jointLaw (signedRank σ) (fun ω => (ω.1, ω.2.2.X, S.state ω)) ≤ η * d) ∧
    (∀ a δ : ℝ, 0 < a → 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ (k : ℕ) [NeZero k], KeyBase k → ∀ (d : ℕ) (Ρ G : Type) [AddCommGroup G]
        (S : NoisySketch d k Ρ G) (σ : Ρ → Str d k → ℝ), IsSign σ →
          condVar S.jointLaw (signedRank σ) (fun ω => (ω.1, ω.2.2.X, S.state ω)) ≤ η * d →
          prob S.jointLaw
              {ω | a * Real.sqrt d <
                |condExp S.jointLaw (signedRank σ) (fun ω' => (ω'.1, ω'.2.2.X, S.state ω')) ω -
                  signedRank σ ω|} ≤ δ) := by sorry

end TurnstileRank.TightBounds
