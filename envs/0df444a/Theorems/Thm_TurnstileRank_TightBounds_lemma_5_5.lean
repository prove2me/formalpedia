-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_lemma_5_5
-- name    : TurnstileRank.TightBounds.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:10:17.29321+00:00
-- url     : https://prove2.me/theorems/16e56acc-a28e-4a4b-90dd-def859809696
-- title:
--   Lemma 5.5 — small error: I(V_{1:d} ; M | ρ) = Ω(d²)
-- statement:
--   Lemma 5.5 (Small error). Let r ≥ 1 with εr√d ≤ a0/3, and suppose a linear sketch errs by more than ε‖f‖1 with probability at most δ0 on every fixed input f of mass at most n, where a0, δ0 are the constants of Theorem 4.5. Let V be a hard instance with weight w ≤ n/(2rd), and let Z be an input independent of V and ρ, of mass less than (2r − 1)dw, at most εrdw of it in the block of V, and with a fixed mass before that block. Then the state M on V + Z satisfies I(V_{1:d} ; M | ρ) = Ω(d²).
--
--   In Lean: for all $a_0,\delta_0,c_{45}>0$ for which Theorem 4.5 holds (`DecodingBound a₀ δ₀ c₄₅`) there is $c>0$ such that for every admissible base $k$, every $0<\varepsilon\le1/8$, all $U,n,d$ and $r\ge1$ with $\varepsilon r\sqrt d\le a_0/3$, every linear sketch with failure probability at most $\delta_0$ on inputs of mass at most $n$, every block $[o,o+k^d)\subseteq[U]$, every weight $w\ge1$ with $w\le n/(2rd)$, and every random input $Z$ independent of $V$ and $\rho$ with $\|Z\|_1<(2r-1)dw$, mass at most $\varepsilon rdw$ in the block and a fixed mass before the block: $I(V_{1:d};A_\rho(V+Z)\mid\rho)\ge cd^2$.
--
--   Differences from the source:
--   - reading: "where a₀, δ₀ are the constants of Theorem 4.5" → any a₀, δ₀ > 0 (with some c₄₅ > 0) for which the statement of Theorem 4.5 holds (`DecodingBound`); reason: Theorem 4.5 only asserts that such constants exist; the lemma's proof uses nothing about them but Theorem 4.5 itself, so it holds for every valid choice
--   - encoding: Ω(d²) → ∃ c > 0, chosen after a₀, δ₀, c₄₅ and before every other parameter; reason: O(·)/Ω(·) with an absolute constant uniform over all parameters, made explicit and quantified before them
--   - encoding: Definition 3.1: a public seed ρ (a bit string) fixing G_ρ, A_ρ, g_ρ; space = least s with at most 2^s states for every seed → `LinearSketch`: a discrete seed law, one group G, item map and decoder; `HasSpace L s`: for every seed in the support the state set {A_ρ(f) : f ∈ ℤ^U} is finite with at most 2^s elements; "a sketch of s bits" is `HasSpace L s`; reason: a bit-string seed is a discrete random variable, and seeds outside the support never occur; the groups G_ρ embed in one product group
--   - encoding: an abelian group G_ρ that depends on the seed ρ → one abelian group G for every seed; reason: the groups G_ρ embed in the product Π_ρ G_ρ, which changes no state and no information quantity
--   - encoding: strings of [k]^d with 1-indexed digits X[1..d] and levels i = 1..d → `Str d k = Fin d → Fin k` with 0-based digit positions and item indices (paper level i is `i.val + 1`, digit X[j] is `X ⟨j − 1⟩`); reason: a bijective reindexing; `strVal` is the lexicographic order, most significant digit first
--   - encoding: V_i uniform among strings agreeing with X in their first i − 1 digits, independently given X → V_i copies X before position i and an independent uniform string W_i from position i on (`splice`); reason: the same joint law of (X, V_1, …, V_d)
--   - reading: fix a sufficiently large power of two k with k⁻¹ ≤ η₀/8 (§4.1) → every power of two k with k⁻¹ ≤ η₀/8 (`KeyBase k`), quantified after the absolute constants; reason: the section's proofs use only k⁻¹ ≤ η₀/8, and its constants do not depend on k; holding for every such k is the stronger reading of "fix"
--   - encoding: Z an input (a nonnegative frequency vector) independent of V and ρ, with bounds on its masses → Z has an arbitrary discrete law ζ on ℕ^U, independent of the seed and the instance (`blockInfo`), and every bound holds for every z in the support of ζ; reason: an input is a nonnegative integer vector; a bound on a random input holds almost surely, i.e. on the support
--   - encoding: I(A ; B | C) := H(A | C) − H(A | B, C) in bits → `condMI P A B C` = Σ_{b,c} P[B = b, C = c] · D_KL(P_{A|b,c} ‖ P_{A|c}) in bits, valued in ℝ≥0∞, for a finite-valued A; reason: equal to H(A | C) − H(A | B, C) whenever A is finite-valued, which holds in every use; ℝ≥0∞ avoids summability side conditions and the value is finite
--   - encoding: universe [U] = {0, …, U − 1}; queries x ∈ {0, …, U} → `Fin U`; queries `x : ℕ` with `x ≤ U`; reason: same objects
--   - encoding: an instance inserted with weight w in an integer frequency vector → w : ℕ with 1 ≤ w; reason: positive integer multiplicities are the weights of the turnstile input; zero weight is not an inserted instance
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Lemma 5.5, printed p. 26 (PDF 27)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_Blocks

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Lemma 5.5 (Small error), for the constants `a₀, δ₀` of Theorem 4.5: for any `a₀, δ₀, c₄₅ > 0`
for which Theorem 4.5 holds (`DecodingBound a₀ δ₀ c₄₅`), the information is `Ω(d²)`. -/
theorem lemma_5_5 :
    ∀ a0 δ0 c45 : ℝ, 0 < a0 → 0 < δ0 → 0 < c45 → DecodingBound a0 δ0 c45 →
    ∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ) [NeZero k], KeyBase k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 8 →
      ∀ (U n d r : ℕ), 1 ≤ r → ε * r * Real.sqrt d ≤ a0 / 3 →
      ∀ (Ρ G : Type) [AddCommGroup G] (L : LinearSketch U Ρ G ℕ ℝ),
        SketchRankCorrect L n ε δ0 →
        ∀ o w : ℕ, o + k ^ d ≤ U → 1 ≤ w → (w : ℝ) ≤ (n : ℝ) / (2 * r * d) →
        ∀ ζ : PMF (Fin U → ℕ),
          (∀ z ∈ ζ.support, (totalMass z : ℝ) < (2 * r - 1) * d * w ∧
            (massIn z o (o + k ^ d) : ℝ) ≤ ε * r * d * w) →
          (∃ m0 : ℕ, ∀ z ∈ ζ.support, massIn z 0 o = m0) →
          ENNReal.ofReal (c * (d : ℝ) ^ 2) ≤
            blockInfo L (hardLaw d k) ζ (fun h => fun i => h.V i) (hardVec U o w) := by sorry

end TurnstileRank.TightBounds
