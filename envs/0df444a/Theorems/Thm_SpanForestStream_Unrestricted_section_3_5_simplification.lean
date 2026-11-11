-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_section_3_5_simplification
-- name    : SpanForestStream.Unrestricted.section_3_5_simplification
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:31:54.137201+00:00
-- url     : https://prove2.me/theorems/f0ae1e24-6841-4a9a-b7a5-c3274f44b23f
-- title:
--   §3.5, final simplification — log(v/δ) ≤ A + t ≤ 2 log(v/δ), log(v/δ) ≤ A + τ₀ ≤ 4 log(v/δ), and the 1/c–c comparison
-- statement:
--   Let $v\ge 2$, $0<\delta\le 1/4$, $A=\lceil\log_2(v+1)\rceil$, $t=1+\log_2(1/\delta)$ and $\tau_0=\lceil\log_2(64/\delta)\rceil$. Then $\log_2 v\le A\le\log_2 v+1$ and $\log_2(1/\delta)\ge 2$, and these give
--   $$\log_2(v/\delta)\le A+t\le 2\log_2(v/\delta),\qquad \log_2(v/\delta)\le A+\tau_0\le 4\log_2(v/\delta).$$
--   For any $u>0$ and $c\ge 1$,
--   $$\tfrac1c\log_2(2+v/u)\le\log_2\big(2+v/(cu)\big)\le\log_2(2+v/u),$$
--   so replacing $u$ by $cu$ in $g(u)=vu\log_2^2(2+v/u)$ changes its value by a factor between $1/c$ and $c$: $\frac1c g(u)\le g(cu)\le c\,g(u)$. Taking the minimum with $v^2$ preserves this comparison.
--
--   These comparisons turn the bound in $A+t$ of Proposition 3.6 into the bound in $\log_2(v/\delta)$ of Theorems 1.1 and 1.2.
--
--   Differences from the source:
--   - encoding: 'changes its value by a factor between 1/c and c; taking the minimum with v² preserves this comparison' → the two-sided inequalities (1/c)g(u) ≤ g(cu) ≤ c·g(u) and the same with min{v², ·}; reason: the meaning of 'a factor between 1/c and c'
--   - encoding: 'log v ≤ A ≤ log v + 1 and log(1/δ) ≥ 2 give' → these premises are also stated as conclusions; reason: they are facts about v ≥ 2 and δ ≤ 1/4 that the passage uses
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 22 (PDF 25), §3.5, final simplification

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_SpaceFunction

namespace SpanForestStream.Unrestricted

/-- §3.5, final simplification: for `v ≥ 2` and `0 < δ ≤ 1/4`, `log₂ v ≤ A ≤ log₂ v + 1` and
`log₂(1/δ) ≥ 2`, `log₂(v/δ) ≤ A + t ≤ 2 log₂(v/δ)`, `log₂(v/δ) ≤ A + τ₀ ≤ 4 log₂(v/δ)`; and for every
`u > 0` and `c ≥ 1`, `(1/c) log₂(2 + v/u) ≤ log₂(2 + v/(cu)) ≤ log₂(2 + v/u)`, so replacing `u` by
`cu` in `v u log₂²(2 + v/u)` changes it by a factor between `1/c` and `c`, also after taking the
minimum with `v²`. -/
theorem section_3_5_simplification (v : ℕ) (hv : 2 ≤ v) (δ : ℝ) (hδ₀ : 0 < δ) (hδ : δ ≤ 1 / 4) :
    Real.logb 2 v ≤ ceilLog v ∧ (ceilLog v : ℝ) ≤ Real.logb 2 v + 1 ∧
    2 ≤ Real.logb 2 (1 / δ) ∧
    Real.logb 2 (v / δ) ≤ ceilLog v + confT δ ∧
    (ceilLog v : ℝ) + confT δ ≤ 2 * Real.logb 2 (v / δ) ∧
    Real.logb 2 (v / δ) ≤ ceilLog v + tau0 δ ∧
    ((ceilLog v : ℝ) + tau0 δ) ≤ 4 * Real.logb 2 (v / δ) ∧
    ∀ u c : ℝ, 0 < u → 1 ≤ c →
      (1 / c) * Real.logb 2 (2 + v / u) ≤ Real.logb 2 (2 + v / (c * u)) ∧
      Real.logb 2 (2 + v / (c * u)) ≤ Real.logb 2 (2 + v / u) ∧
      (1 / c) * (v * u * Real.logb 2 (2 + v / u) ^ 2) ≤
        v * (c * u) * Real.logb 2 (2 + v / (c * u)) ^ 2 ∧
      v * (c * u) * Real.logb 2 (2 + v / (c * u)) ^ 2 ≤
        c * (v * u * Real.logb 2 (2 + v / u) ^ 2) ∧
      (1 / c) * min ((v : ℝ) ^ 2) (v * u * Real.logb 2 (2 + v / u) ^ 2) ≤
        min ((v : ℝ) ^ 2) (v * (c * u) * Real.logb 2 (2 + v / (c * u)) ^ 2) ∧
      min ((v : ℝ) ^ 2) (v * (c * u) * Real.logb 2 (2 + v / (c * u)) ^ 2) ≤
        c * min ((v : ℝ) ^ 2) (v * u * Real.logb 2 (2 + v / u) ^ 2) := by sorry

end SpanForestStream.Unrestricted
