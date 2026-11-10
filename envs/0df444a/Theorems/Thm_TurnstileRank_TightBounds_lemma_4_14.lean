-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_lemma_4_14
-- name    : TurnstileRank.TightBounds.lemma_4_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:08:41.486833+00:00
-- url     : https://prove2.me/theorems/ad94b9f9-2bbc-4e31-b96a-cc61f85c571c
-- title:
--   Lemma 4.14 — variance partition
-- statement:
--   Lemma 4.14 (Variance partition). We have the exact identity Var(R̃ | X, A_ρ(V_{1:d}; N)) = Σ_{i=1}^{d} Var_i. (4.8)
--
--   In Lean: for every admissible base $k$, every $d$, every linear sketch with noise and every sign function, $\mathrm{Var}(\tilde R\mid\rho,X,A_\rho(V_{1:d};N))=\sum_{i}\mathrm{Var}_i$, with $\mathrm{Var}_i$ the digitwise variance of Definition 4.13.
--
--   Differences from the source:
--   - encoding: strings of [k]^d with 1-indexed digits X[1..d] and levels i = 1..d → `Str d k = Fin d → Fin k` with 0-based digit positions and item indices (paper level i is `i.val + 1`, digit X[j] is `X ⟨j − 1⟩`); reason: a bijective reindexing; `strVal` is the lexicographic order, most significant digit first
--   - encoding: random variables (public randomness, noise, hard instance) on an unspecified probability space → one discrete law (`PMF`) on the sample type `Ρ × G × HardSample d k`; probabilities by `prob`; reason: all quantities of §3.2 are sums over values, i.e. the variables are discrete; a PMF may live on an uncountable type with countable support
--   - encoding: an abelian group G_ρ that depends on the seed ρ → one abelian group G for every seed; reason: the groups G_ρ embed in the product Π_ρ G_ρ, which changes no state and no information quantity
--   - encoding: ρ independent of (X, V_{1:d}); noise N independent of (X, V_{1:d}) given ρ → (ρ, N) has an arbitrary discrete joint law `S.law`, independent of the hard instance (`NoisySketch.jointLaw`); reason: the two independence statements together say exactly that (ρ, N) is independent of (X, V_{1:d})
--   - encoding: V_i uniform among strings agreeing with X in their first i − 1 digits, independently given X → V_i copies X before position i and an independent uniform string W_i from position i on (`splice`); reason: the same joint law of (X, V_1, …, V_d)
--   - reading: fix a sufficiently large power of two k with k⁻¹ ≤ η₀/8 (§4.1) → every power of two k with k⁻¹ ≤ η₀/8 (`KeyBase k`), quantified after the absolute constants; reason: the section's proofs use only k⁻¹ ≤ η₀/8, and its constants do not depend on k; holding for every such k is the stronger reading of "fix"
--   - encoding: Var(Z | C) of Definition 4.9, with ρ suppressed from the conditioning ("Where not displayed explicitly, ρ is suppressed", p. 16) → `condVar P Z C` = the number E[(Z − E[Z | C])²], with ρ inside every conditioning variable C; reason: Definition 4.9 and the paper's convention verbatim; every Z used is bounded, so the infinite sums converge
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Lemma 4.14, printed p. 17 (PDF 18)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_HardInstance

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Lemma 4.14 (Variance partition): `Var(R̃ | X, A_ρ(V_{1:d}; N)) = Σ_i Var_i`. -/
theorem lemma_4_14 (k : ℕ) [NeZero k] (hk : KeyBase k) (d : ℕ) {Ρ G : Type} [AddCommGroup G]
    (S : NoisySketch d k Ρ G) (σ : Ρ → Str d k → ℝ) (hσ : IsSign σ) :
    condVar S.jointLaw (digitRank σ) (fun ω => (ω.1, ω.2.2.X, S.state ω)) =
      ∑ i : Fin d, digitVar S σ i := by sorry

end TurnstileRank.TightBounds
