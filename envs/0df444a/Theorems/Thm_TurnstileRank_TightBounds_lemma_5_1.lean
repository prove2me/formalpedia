-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_lemma_5_1
-- name    : TurnstileRank.TightBounds.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:10:08.858665+00:00
-- url     : https://prove2.me/theorems/96752c4c-4ea4-4009-804e-f46766e13caa
-- title:
--   Lemma 5.1 — large error
-- statement:
--   Lemma 5.1 (Large error). There are absolute constants ε0, c > 0 such that the following holds for ε ≤ ε0. Suppose a linear sketch of s bits errs by more than ε‖f‖1 with probability at most 1/3 on every fixed input f of mass at most n. Then there is a linear sketch of O((1 + ε²d)s) bits, with public randomness ρ′, whose state M on V + Z satisfies I(V_{1:d} ; M | ρ′) ≥ cd² whenever V is a hard instance with weight w ≤ n/(2d), and Z is an input independent of V and ρ′, of mass at most dw, at most εdw of it in the block of V.
--
--   In Lean: there are $\varepsilon_0,c,C>0$ such that for every admissible base $k$, every $0<\varepsilon\le\varepsilon_0$, all $U,n,d$ and every linear sketch $L$ on $[U]$ with `HasSpace L s` and failure probability at most $1/3$ on inputs of mass at most $n$, there is a linear sketch $L'$ on $[U]$ (seed $\rho'$) with `HasSpace L' (C(1+ε²d)s)` such that for every block $[o,o+k^d)\subseteq[U]$, every weight $w\ge1$ with $w\le n/(2d)$, and every random input $Z$ independent of the hard instance and $\rho'$ with $\|Z\|_1\le dw$ and mass at most $\varepsilon dw$ in the block: $I(V_{1:d};A'_{\rho'}(V+Z)\mid\rho')\ge cd^2$, where $V$ is the hard instance placed on the block with weight $w$.
--
--   Differences from the source:
--   - encoding: Definition 3.1: a public seed ρ (a bit string) fixing G_ρ, A_ρ, g_ρ; space = least s with at most 2^s states for every seed → `LinearSketch`: a discrete seed law, one group G, item map and decoder; `HasSpace L s`: for every seed in the support the state set {A_ρ(f) : f ∈ ℤ^U} is finite with at most 2^s elements; "a sketch of s bits" is `HasSpace L s`; reason: a bit-string seed is a discrete random variable, and seeds outside the support never occur; the groups G_ρ embed in one product group
--   - encoding: an abelian group G_ρ that depends on the seed ρ → one abelian group G for every seed; reason: the groups G_ρ embed in the product Π_ρ G_ρ, which changes no state and no information quantity
--   - encoding: strings of [k]^d with 1-indexed digits X[1..d] and levels i = 1..d → `Str d k = Fin d → Fin k` with 0-based digit positions and item indices (paper level i is `i.val + 1`, digit X[j] is `X ⟨j − 1⟩`); reason: a bijective reindexing; `strVal` is the lexicographic order, most significant digit first
--   - encoding: V_i uniform among strings agreeing with X in their first i − 1 digits, independently given X → V_i copies X before position i and an independent uniform string W_i from position i on (`splice`); reason: the same joint law of (X, V_1, …, V_d)
--   - reading: fix a sufficiently large power of two k with k⁻¹ ≤ η₀/8 (§4.1) → every power of two k with k⁻¹ ≤ η₀/8 (`KeyBase k`), quantified after the absolute constants; reason: the section's proofs use only k⁻¹ ≤ η₀/8, and its constants do not depend on k; holding for every such k is the stronger reading of "fix"
--   - encoding: Z an input (a nonnegative frequency vector) independent of V and ρ, with bounds on its masses → Z has an arbitrary discrete law ζ on ℕ^U, independent of the seed and the instance (`blockInfo`), and every bound holds for every z in the support of ζ; reason: an input is a nonnegative integer vector; a bound on a random input holds almost surely, i.e. on the support
--   - encoding: I(A ; B | C) := H(A | C) − H(A | B, C) in bits → `condMI P A B C` = Σ_{b,c} P[B = b, C = c] · D_KL(P_{A|b,c} ‖ P_{A|c}) in bits, valued in ℝ≥0∞, for a finite-valued A; reason: equal to H(A | C) − H(A | B, C) whenever A is finite-valued, which holds in every use; ℝ≥0∞ avoids summability side conditions and the value is finite
--   - encoding: a linear sketch of O((1 + ε²d)s) bits; absolute constants ε₀, c → `HasSpace L' (C * (1 + ε^2 * d) * s)` with ε₀, c, C > 0 quantified before k, ε, U, n, d and the sketch; reason: O(·)/Ω(·) with an absolute constant uniform over all parameters, made explicit and quantified before them
--   - encoding: universe [U] = {0, …, U − 1}; queries x ∈ {0, …, U} → `Fin U`; queries `x : ℕ` with `x ≤ U`; reason: same objects
--   - encoding: an instance inserted with weight w in an integer frequency vector → w : ℕ with 1 ≤ w; reason: positive integer multiplicities are the weights of the turnstile input; zero weight is not an inserted instance
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Lemma 5.1, printed p. 24 (PDF 25)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_Blocks

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Lemma 5.1 (Large error). -/
theorem lemma_5_1 :
    ∃ ε0 c C : ℝ, 0 < ε0 ∧ 0 < c ∧ 0 < C ∧
      ∀ (k : ℕ) [NeZero k], KeyBase k → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
      ∀ (U n d : ℕ) (Ρ G : Type) [AddCommGroup G] (L : LinearSketch U Ρ G ℕ ℝ) (s : ℝ),
        L.HasSpace s → SketchRankCorrect L n ε (1 / 3) →
        ∃ (Ρ' G' : Type) (_ : AddCommGroup G') (L' : LinearSketch U Ρ' G' ℕ ℝ),
          L'.HasSpace (C * (1 + ε ^ 2 * d) * s) ∧
          ∀ o w : ℕ, o + k ^ d ≤ U → 1 ≤ w → (w : ℝ) ≤ (n : ℝ) / (2 * d) →
          ∀ ζ : PMF (Fin U → ℕ),
            (∀ z ∈ ζ.support, totalMass z ≤ d * w ∧ (massIn z o (o + k ^ d) : ℝ) ≤ ε * d * w) →
            ENNReal.ofReal (c * (d : ℝ) ^ 2) ≤
              blockInfo L' (hardLaw d k) ζ (fun h => fun i => h.V i) (hardVec U o w) := by sorry

end TurnstileRank.TightBounds
