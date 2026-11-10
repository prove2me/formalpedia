-- Prove2me | Theorems.Thm_TurnstileRank_TightBounds_corollary_5_6
-- name    : TurnstileRank.TightBounds.corollary_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:08:57.638943+00:00
-- url     : https://prove2.me/theorems/7f881af8-7401-4f79-a9ae-cb5b9d3c5025
-- title:
--   Corollary 5.6 — linear sketches need Ω(RQ(ε, n, U)) bits
-- statement:
--   Corollary 5.6 (Lower bound for linear sketches). Let U ≥ 4 and n ≥ log² U. Then every linear sketch correct with failure probability at most 1/3 on inputs of mass at most n uses Ω(RQ(ε, n, U)) bits.
--
--   Standing assumption of §5: $0<\varepsilon\le1/8$ (p. 23).
--
--   In Lean: there is $c>0$ such that for all $U\ge4$, $n\ge(\log_2U)^2$ and $0<\varepsilon\le1/8$, every linear sketch $L$ on $[U]$ with failure probability at most $1/3$ on inputs of mass at most $n$ (`SketchRankCorrect L n ε (1/3)`) and every $s$ with `HasSpace L s` satisfy $c\cdot RQ(\varepsilon,n,U)\le s$.
--
--   Differences from the source:
--   - encoding: Definition 3.1: a public seed ρ (a bit string) fixing G_ρ, A_ρ, g_ρ; space = least s with at most 2^s states for every seed → `LinearSketch`: a discrete seed law, one group G, item map and decoder; `HasSpace L s`: for every seed in the support the state set {A_ρ(f) : f ∈ ℤ^U} is finite with at most 2^s elements; "a sketch of s bits" is `HasSpace L s`; reason: a bit-string seed is a discrete random variable, and seeds outside the support never occur; the groups G_ρ embed in one product group
--   - encoding: Ω(RQ(ε, n, U)) bits → ∃ c > 0 before U, n, ε and the sketch, with c · RQ ε n U ≤ s; reason: O(·)/Ω(·) with an absolute constant uniform over all parameters, made explicit and quantified before them
--   - encoding: universe [U] = {0, …, U − 1}; queries x ∈ {0, …, U} → `Fin U`; queries `x : ℕ` with `x ≤ U`; reason: same objects
--   - encoding: log (base two, §3.2) → `Real.logb 2`; reason: the paper's convention
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Corollary 5.6, printed p. 27 (PDF 28)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_LinearSketch

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Corollary 5.6 (Lower bound for linear sketches): for `U ≥ 4`, `n ≥ log₂² U` and
`0 < ε ≤ 1/8`, every linear sketch correct with failure probability at most `1/3` on inputs of mass
at most `n` uses `Ω(RQ(ε, n, U))` bits. -/
theorem corollary_5_6 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (U n : ℕ) (ε : ℝ), 4 ≤ U → Real.logb 2 U ^ 2 ≤ n → 0 < ε → ε ≤ 1 / 8 →
      ∀ (Ρ G : Type) [AddCommGroup G] (L : LinearSketch U Ρ G ℕ ℝ) (s : ℝ),
        L.HasSpace s → SketchRankCorrect L n ε (1 / 3) → c * RQ ε n U ≤ s := by sorry

end TurnstileRank.TightBounds
