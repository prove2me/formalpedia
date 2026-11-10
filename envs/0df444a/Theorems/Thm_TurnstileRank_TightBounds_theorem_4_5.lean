-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_theorem_4_5
-- name    : TurnstileRank.TightBounds.theorem_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:11:43.321207+00:00
-- url     : https://prove2.me/theorems/874991c0-2726-42b9-b36a-f92adc8454dc
-- title:
--   Theorem 4.5 — decoding forces information
-- statement:
--   Theorem 4.5 (Decoding forces information). For absolute constants a0, δ0, c > 0, if P[|T − R| > a0√d] ≤ δ0 (4.3) then I(V_{1:d} ; A_ρ(V_{1:d}; N) | ρ) ≥ cd². (4.4) Here, the probability averages over the hard instance, public randomness, and noise.
--
--   In Lean: there are $a_0,\delta_0,c>0$ with `DecodingBound a₀ δ₀ c`: for every admissible base $k$, every $d$, every linear sketch with noise $(\rho,N,A_\rho)$, every sign function $\sigma_\rho$ and every estimate $T(\rho,X,A_\rho(V_{1:d};N))$, if $P[|T-R|>a_0\sqrt d]\le\delta_0$ then $I(V_{1:d};A_\rho(V_{1:d};N)\mid\rho)\ge cd^2$.
--
--   Differences from the source:
--   - encoding: strings of [k]^d with 1-indexed digits X[1..d] and levels i = 1..d → `Str d k = Fin d → Fin k` with 0-based digit positions and item indices (paper level i is `i.val + 1`, digit X[j] is `X ⟨j − 1⟩`); reason: a bijective reindexing; `strVal` is the lexicographic order, most significant digit first
--   - encoding: random variables (public randomness, noise, hard instance) on an unspecified probability space → one discrete law (`PMF`) on the sample type `Ρ × G × HardSample d k`; probabilities by `prob`; reason: all quantities of §3.2 are sums over values, i.e. the variables are discrete; a PMF may live on an uncountable type with countable support
--   - encoding: an abelian group G_ρ that depends on the seed ρ → one abelian group G for every seed; reason: the groups G_ρ embed in the product Π_ρ G_ρ, which changes no state and no information quantity
--   - encoding: ρ independent of (X, V_{1:d}); noise N independent of (X, V_{1:d}) given ρ → (ρ, N) has an arbitrary discrete joint law `S.law`, independent of the hard instance (`NoisySketch.jointLaw`); reason: the two independence statements together say exactly that (ρ, N) is independent of (X, V_{1:d})
--   - encoding: V_i uniform among strings agreeing with X in their first i − 1 digits, independently given X → V_i copies X before position i and an independent uniform string W_i from position i on (`splice`); reason: the same joint law of (X, V_1, …, V_d)
--   - reading: fix a sufficiently large power of two k with k⁻¹ ≤ η₀/8 (§4.1) → every power of two k with k⁻¹ ≤ η₀/8 (`KeyBase k`), quantified after the absolute constants; reason: the section's proofs use only k⁻¹ ≤ η₀/8, and its constants do not depend on k; holding for every such k is the stronger reading of "fix"
--   - encoding: an estimate T of R → any function `T ρ X M` of the seed, the query and the final state; reason: the decoder sees exactly (ρ, X, A_ρ(V_{1:d}; N)) (proof of Lemma 4.10: "T̂ is determined by (X, A_ρ(V_{1:d}; N), ρ)")
--   - encoding: I(A ; B | C) := H(A | C) − H(A | B, C) in bits → `condMI P A B C` = Σ_{b,c} P[B = b, C = c] · D_KL(P_{A|b,c} ‖ P_{A|c}) in bits, valued in ℝ≥0∞, for a finite-valued A; reason: equal to H(A | C) − H(A | B, C) whenever A is finite-valued, which holds in every use; ℝ≥0∞ avoids summability side conditions and the value is finite
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Theorem 4.5, printed p. 14 (PDF 15)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_HardInstance

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Theorem 4.5 (Decoding forces information): there are absolute constants `a₀, δ₀, c > 0` such
that `P[|T − R| > a₀√d] ≤ δ₀` implies `I(V_{1:d} ; A_ρ(V_{1:d}; N) | ρ) ≥ cd²`
(`DecodingBound a₀ δ₀ c`). -/
theorem theorem_4_5 :
    ∃ a0 δ0 c : ℝ, 0 < a0 ∧ 0 < δ0 ∧ 0 < c ∧ DecodingBound a0 δ0 c := by sorry

end TurnstileRank.TightBounds
