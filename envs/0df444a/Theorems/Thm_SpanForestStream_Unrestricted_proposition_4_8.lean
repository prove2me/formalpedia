-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_proposition_4_8
-- name    : SpanForestStream.Unrestricted.proposition_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:40.692353+00:00
-- url     : https://prove2.me/theorems/a32b3d78-622e-4165-b3c5-820f687bc32f
-- title:
--   Proposition 4.8 — spanning-forest lower bound from indexed graph blocks (error 1/4)
-- statement:
--   There are absolute constants $k_0,C_1,C_2,c>0$ such that the following holds. Suppose $N=hk$ with $k\ge k_0$ even, $m\ge C_1\log_2(k+1)$, $U\ge C_2m$, $N+U\le v$ and $k(m-1)\le Z$. Let an algorithm on $[v]$ have error at most $1/4$ on every fixed legal stream consisting of exactly $Nm$ insertions followed by at most $k(m-1)$ deletions and one report; each such stream has at most $Z$ deletion operations. Then, for either space measure $s$ (worst-case or worst-input expected peak space),
--   $$s+1\ge c\,N\log_2(k+1)\,\log_2\Big(2+\frac{m}{\log_2(k+1)}\Big)\log_2\frac Um.\qquad(4.20)$$
--
--   Combined with the insertion-only baseline, this gives the constant-error lower bound of Corollary 4.9.
--
--   Differences from the source:
--   - reading: k, m, U 'satisfy the preceding proposition' → k ≥ k0 even, m ≥ C1 log₂(k+1), U ≥ C2 m for absolute k0, C1, C2 existentially quantified with the theorem; reason: Proposition 4.7's thresholds are themselves existential absolute constants
--   - generalization: error ≤ 1/4 on every fixed legal stream with at most Z deletions; 'the hard streams are legal, have exactly Nm insertions followed by at most k(m − 1) ≤ Z deletions, and request one report' → the error hypothesis only on legal streams of exactly N·m insertions followed by at most k(m − 1) deletions; reason: the hypothesis is weaker (only the hard streams), so the statement is more general; it specializes to the printed one because each such stream is legal with at most k(m − 1) ≤ Z deletions, so the main sentence's hypothesis implies it, and the hard-streams clause asserts these are the only streams the bound needs
--   - encoding: Ω(·), s + 1, 'either space measure' → ∃ absolute c > 0; both c·(…) ≤ expPeak + 1 and c·(…) ≤ hardPeak + 1, in [0,∞]; reason: App. A: space is peak + 1
--   - encoding: m − 1 → natural-number subtraction; reason: m ≥ 1 whenever k ≥ 1, so it agrees with the source
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 31 (PDF 34), Proposition 4.8, Eq. (4.20)

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Stream
import Definitions.Def_SpanForestStream_Unrestricted_Transducer

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Proposition 4.8 (spanning-forest lower bound from indexed graph blocks): there are absolute
`k₀, C₁, C₂, c > 0` such that if `N = hk` with `k ≥ k₀` even, `m ≥ C₁ log₂(k+1)`, `U ≥ C₂ m`,
`N + U ≤ v` and `k(m − 1) ≤ Z`, then every algorithm with error at most `1/4` on the legal streams
of exactly `Nm` insertions followed by at most `k(m − 1)` deletions (all of which have at most `Z`
deletions) has, in both space measures,
`s + 1 ≥ c N log₂(k+1) log₂(2 + m / log₂(k+1)) log₂(U/m)`. -/
theorem proposition_4_8 :
    ∃ (k₀ : ℕ) (C₁ C₂ c : ℝ), 0 < C₁ ∧ 0 < C₂ ∧ 0 < c ∧
      ∀ (v N h k m U Z : ℕ), N = h * k → k₀ ≤ k → Even k →
        C₁ * Real.logb 2 (k + 1) ≤ m → C₂ * m ≤ U → N + U ≤ v → k * (m - 1) ≤ Z →
        ∀ A : Transducer v,
          (∀ w : List (Update v), IsLegal w → IsInsThenDel w (N * m) (k * (m - 1)) →
            A.errorProb w ≤ 1 / 4) →
          ENNReal.ofReal (c * N * Real.logb 2 (k + 1) *
              Real.logb 2 (2 + m / Real.logb 2 (k + 1)) * Real.logb 2 (U / m)) ≤
              A.expPeak + 1 ∧
          ENNReal.ofReal (c * N * Real.logb 2 (k + 1) *
              Real.logb 2 (2 + m / Real.logb 2 (k + 1)) * Real.logb 2 (U / m)) ≤
              A.hardPeak + 1 := by sorry

end SpanForestStream.Unrestricted
