-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_lemma_4_12
-- name    : TurnstileRank.TightBounds.lemma_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:11:45.749522+00:00
-- url     : https://prove2.me/theorems/1af6eda4-2e51-4a24-a600-b4b10719da03
-- title:
--   Lemma 4.12 — variance form
-- statement:
--   Lemma 4.12 (Variance form). There exist absolute constants η, c > 0 such that if Var(R | X, A_ρ(V_{1:d}; N), ρ) ≤ ηd, then I(V_{1:d} ; A_ρ(V_{1:d}; N) | ρ) ≥ cd². (4.7)
--
--   In Lean: there are $\eta,c>0$ such that for every admissible base $k$, every $d$, every linear sketch with noise and every sign function: $\mathrm{Var}(R\mid\rho,X,A_\rho(V_{1:d};N))\le\eta d$ implies $I(V_{1:d};A_\rho(V_{1:d};N)\mid\rho)\ge cd^2$.
--
--   Differences from the source:
--   - encoding: strings of [k]^d with 1-indexed digits X[1..d] and levels i = 1..d → `Str d k = Fin d → Fin k` with 0-based digit positions and item indices (paper level i is `i.val + 1`, digit X[j] is `X ⟨j − 1⟩`); reason: a bijective reindexing; `strVal` is the lexicographic order, most significant digit first
--   - encoding: random variables (public randomness, noise, hard instance) on an unspecified probability space → one discrete law (`PMF`) on the sample type `Ρ × G × HardSample d k`; probabilities by `prob`; reason: all quantities of §3.2 are sums over values, i.e. the variables are discrete; a PMF may live on an uncountable type with countable support
--   - encoding: an abelian group G_ρ that depends on the seed ρ → one abelian group G for every seed; reason: the groups G_ρ embed in the product Π_ρ G_ρ, which changes no state and no information quantity
--   - encoding: ρ independent of (X, V_{1:d}); noise N independent of (X, V_{1:d}) given ρ → (ρ, N) has an arbitrary discrete joint law `S.law`, independent of the hard instance (`NoisySketch.jointLaw`); reason: the two independence statements together say exactly that (ρ, N) is independent of (X, V_{1:d})
--   - encoding: V_i uniform among strings agreeing with X in their first i − 1 digits, independently given X → V_i copies X before position i and an independent uniform string W_i from position i on (`splice`); reason: the same joint law of (X, V_1, …, V_d)
--   - reading: fix a sufficiently large power of two k with k⁻¹ ≤ η₀/8 (§4.1) → every power of two k with k⁻¹ ≤ η₀/8 (`KeyBase k`), quantified after the absolute constants; reason: the section's proofs use only k⁻¹ ≤ η₀/8, and its constants do not depend on k; holding for every such k is the stronger reading of "fix"
--   - encoding: Var(Z | C) of Definition 4.9, with ρ suppressed from the conditioning ("Where not displayed explicitly, ρ is suppressed", p. 16) → `condVar P Z C` = the number E[(Z − E[Z | C])²], with ρ inside every conditioning variable C; reason: Definition 4.9 and the paper's convention verbatim; every Z used is bounded, so the infinite sums converge
--   - encoding: I(A ; B | C) := H(A | C) − H(A | B, C) in bits → `condMI P A B C` = Σ_{b,c} P[B = b, C = c] · D_KL(P_{A|b,c} ‖ P_{A|c}) in bits, valued in ℝ≥0∞, for a finite-valued A; reason: equal to H(A | C) − H(A | B, C) whenever A is finite-valued, which holds in every use; ℝ≥0∞ avoids summability side conditions and the value is finite
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Lemma 4.12, printed p. 17 (PDF 18)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_HardInstance

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Lemma 4.12 (Variance form): absolute `η, c > 0` such that
`Var(R | X, A_ρ(V_{1:d}; N), ρ) ≤ ηd` implies `I(V_{1:d} ; A_ρ(V_{1:d}; N) | ρ) ≥ cd²`. -/
theorem lemma_4_12 :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      ∀ (k : ℕ) [NeZero k], KeyBase k → ∀ (d : ℕ) (Ρ G : Type) [AddCommGroup G]
        (S : NoisySketch d k Ρ G) (σ : Ρ → Str d k → ℝ), IsSign σ →
          condVar S.jointLaw (signedRank σ) (fun ω => (ω.1, ω.2.2.X, S.state ω)) ≤ η * d →
          ENNReal.ofReal (c * (d : ℝ) ^ 2) ≤
            condMI S.jointLaw (fun ω => fun i => ω.2.2.V i) S.state (fun ω => ω.1) := by sorry

end TurnstileRank.TightBounds
