-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_lemma_4_16
-- name    : TurnstileRank.TightBounds.lemma_4_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:08:25.425104+00:00
-- url     : https://prove2.me/theorems/e50e6e88-f8ef-460a-9b31-6a48d4453ab1
-- title:
--   Lemma 4.16 — diagonal to off-diagonal: I_{i,j} ≥ I_{j,j}
-- statement:
--   Lemma 4.16 (Diagonal to off-diagonal). I_{i,j} ≥ I_{j,j} whenever i ≤ j.
--
--   In Lean: for every admissible base $k$, every $d$, every linear sketch with noise and all levels $i\le j$, $I_{j,j}\le I_{i,j}$ (digitwise information of Definition 4.6).
--
--   Differences from the source:
--   - encoding: strings of [k]^d with 1-indexed digits X[1..d] and levels i = 1..d → `Str d k = Fin d → Fin k` with 0-based digit positions and item indices (paper level i is `i.val + 1`, digit X[j] is `X ⟨j − 1⟩`); reason: a bijective reindexing; `strVal` is the lexicographic order, most significant digit first
--   - encoding: random variables (public randomness, noise, hard instance) on an unspecified probability space → one discrete law (`PMF`) on the sample type `Ρ × G × HardSample d k`; probabilities by `prob`; reason: all quantities of §3.2 are sums over values, i.e. the variables are discrete; a PMF may live on an uncountable type with countable support
--   - encoding: an abelian group G_ρ that depends on the seed ρ → one abelian group G for every seed; reason: the groups G_ρ embed in the product Π_ρ G_ρ, which changes no state and no information quantity
--   - encoding: ρ independent of (X, V_{1:d}); noise N independent of (X, V_{1:d}) given ρ → (ρ, N) has an arbitrary discrete joint law `S.law`, independent of the hard instance (`NoisySketch.jointLaw`); reason: the two independence statements together say exactly that (ρ, N) is independent of (X, V_{1:d})
--   - encoding: V_i uniform among strings agreeing with X in their first i − 1 digits, independently given X → V_i copies X before position i and an independent uniform string W_i from position i on (`splice`); reason: the same joint law of (X, V_1, …, V_d)
--   - reading: fix a sufficiently large power of two k with k⁻¹ ≤ η₀/8 (§4.1) → every power of two k with k⁻¹ ≤ η₀/8 (`KeyBase k`), quantified after the absolute constants; reason: the section's proofs use only k⁻¹ ≤ η₀/8, and its constants do not depend on k; holding for every such k is the stronger reading of "fix"
--   - encoding: I(A ; B | C) := H(A | C) − H(A | B, C) in bits → `condMI P A B C` = Σ_{b,c} P[B = b, C = c] · D_KL(P_{A|b,c} ‖ P_{A|c}) in bits, valued in ℝ≥0∞, for a finite-valued A; reason: equal to H(A | C) − H(A | B, C) whenever A is finite-valued, which holds in every use; ℝ≥0∞ avoids summability side conditions and the value is finite
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Lemma 4.16, printed p. 21 (PDF 22)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_HardInstance

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Lemma 4.16 (Diagonal to off-diagonal): `I_{i,j} ≥ I_{j,j}` whenever `i ≤ j`. -/
theorem lemma_4_16 (k : ℕ) [NeZero k] (hk : KeyBase k) (d : ℕ) {Ρ G : Type} [AddCommGroup G]
    (S : NoisySketch d k Ρ G) (i j : Fin d) (hij : i ≤ j) :
    digitInfo S j j ≤ digitInfo S i j := by sorry

end TurnstileRank.TightBounds
