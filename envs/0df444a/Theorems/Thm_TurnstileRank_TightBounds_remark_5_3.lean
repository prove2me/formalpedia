-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_remark_5_3
-- name    : TurnstileRank.TightBounds.remark_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:12:03.887011+00:00
-- url     : https://prove2.me/theorems/b0a3a987-7868-4f81-9ef4-83c62cce6e26
-- title:
--   Remark 5.3 — single items: I(Y ; M | ρ) ≥ (1 − h₂(1/3))d
-- statement:
--   Remark 5.3 (Single items). For ε > ε0 the buckets are too coarse, and single items suffice instead. Let Y be a uniform point of {0, 1}^d, placed on a block of 2^d consecutive coordinates in lexicographic order with weight w ≤ n/2, and let Z be an input independent of Y and ρ, of mass less than w, at most w/4 of it in the block of Y, and with a fixed mass before that block. Then every linear sketch correct with failure probability at most 1/3 on inputs of mass at most n has I(Y ; M | ρ) ≥ (1 − h2(1/3))d for its state M on Y + Z.
--
--   In Lean: for every $0<\varepsilon\le1/8$, every block $[o,o+2^d)\subseteq[U]$, every weight $w\ge1$ with $2w\le n$, every linear sketch $L$ with failure probability at most $1/3$ on inputs of mass at most $n$, and every random input $Z$ independent of $Y$ and $\rho$ with $\|Z\|_1<w$, $4\cdot(\text{mass of }Z\text{ in the block})\le w$ and a fixed mass before the block: $I(Y;A_\rho(Y+Z)\mid\rho)\ge(1-h_2(1/3))d$, where $Y$ is uniform on $\{0,1\}^d$ (`Str d 2`) and placed with weight $w$ at coordinate $o+\mathrm{strVal}(Y)$.
--
--   Differences from the source:
--   - generalization: "For ε > ε₀ the buckets are too coarse, and single items suffice instead" (ε₀ of Lemma 5.1) → every 0 < ε ≤ 1/8; reason: the remark's argument only uses 2ε + 1/8 < 1/2, and the paper applies it for small ε too (Corollary 5.6, §6); the Lean statement specializes to ε > ε₀
--   - encoding: Definition 3.1: a public seed ρ (a bit string) fixing G_ρ, A_ρ, g_ρ; space = least s with at most 2^s states for every seed → `LinearSketch`: a discrete seed law, one group G, item map and decoder; `HasSpace L s`: for every seed in the support the state set {A_ρ(f) : f ∈ ℤ^U} is finite with at most 2^s elements; "a sketch of s bits" is `HasSpace L s`; reason: a bit-string seed is a discrete random variable, and seeds outside the support never occur; the groups G_ρ embed in one product group
--   - encoding: Z an input (a nonnegative frequency vector) independent of V and ρ, with bounds on its masses → Z has an arbitrary discrete law ζ on ℕ^U, independent of the seed and the instance (`blockInfo`), and every bound holds for every z in the support of ζ; reason: an input is a nonnegative integer vector; a bound on a random input holds almost surely, i.e. on the support
--   - encoding: I(A ; B | C) := H(A | C) − H(A | B, C) in bits → `condMI P A B C` = Σ_{b,c} P[B = b, C = c] · D_KL(P_{A|b,c} ‖ P_{A|c}) in bits, valued in ℝ≥0∞, for a finite-valued A; reason: equal to H(A | C) − H(A | B, C) whenever A is finite-valued, which holds in every use; ℝ≥0∞ avoids summability side conditions and the value is finite
--   - encoding: {0,1}^d in lexicographic order → `Str d 2 = Fin d → Fin 2` with `strVal`, 0-based digits; reason: same points, same order
--   - encoding: an instance inserted with weight w in an integer frequency vector → w : ℕ with 1 ≤ w; reason: positive integer multiplicities are the weights of the turnstile input; zero weight is not an inserted instance
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Remark 5.3, printed p. 25 (PDF 26)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_Blocks

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Remark 5.3 (Single items): a uniform point `Y` of `{0,1}^d` on a block of `2^d` coordinates
with weight `w ≤ n/2`, plus an independent input `Z` of mass `< w`, at most `w/4` of it in the block
and a fixed mass before it, forces `I(Y ; M | ρ) ≥ (1 − h₂(1/3))d`. -/
theorem remark_5_3 (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (U n d o w : ℕ)
    (hblock : o + 2 ^ d ≤ U) (hw : 1 ≤ w) (hwn : 2 * w ≤ n)
    {Ρ G : Type} [AddCommGroup G] (L : LinearSketch U Ρ G ℕ ℝ)
    (hL : SketchRankCorrect L n ε (1 / 3)) (ζ : PMF (Fin U → ℕ))
    (hZ : ∀ z ∈ ζ.support, totalMass z < w ∧ 4 * massIn z o (o + 2 ^ d) ≤ w)
    (hfix : ∃ m0 : ℕ, ∀ z ∈ ζ.support, massIn z 0 o = m0) :
    ENNReal.ofReal ((1 - h2 (1 / 3)) * d) ≤
      blockInfo L (PMF.uniformOfFintype (Str d 2)) ζ id
        (fun y => placeVec U (fun _ : Unit => o + strVal y) w) := by sorry

end TurnstileRank.TightBounds
