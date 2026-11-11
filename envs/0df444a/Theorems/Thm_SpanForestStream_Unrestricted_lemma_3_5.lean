-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_lemma_3_5
-- name    : SpanForestStream.Unrestricted.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:31.585335+00:00
-- url     : https://prove2.me/theorems/b87388e7-17f4-47e2-ab13-a267ebd1009a
-- title:
--   Lemma 3.5 — exact single-row interface: s + 1 = Ω(N L_η log(2 + m/L_η) log(U/m))
-- statement:
--   There are absolute constants $\beta_0,C_0>0$ (and $c>0$ for the $\Omega$) such that, for every integer $Z\ge 0$, every $0<\eta<\beta_0/2$ with $L_\eta=\ln(1/(2\eta))$, and positive integers $N,U,m$ with $m\ge L_\eta$, $U\ge C_0m$, $N+U\le v$ and $m-1\le Z$, every spanning-forest algorithm on $[v]$ with error at most $\eta$ on all legal streams with at most $Z$ deletion operations (one report, simple graphs) has, in both peak-space measures,
--   $$s+1\ge c\,N\,L_\eta\,\log_2(2+m/L_\eta)\,\log_2(U/m).\qquad(3.20)$$
--
--   Differences from the source:
--   - encoding: Ω(·), s + 1 for both peak-space measures → ∃ absolute c > 0; bounds on expPeak + 1 and hardPeak + 1; reason: App. A: space is peak + 1
--   - encoding: m − 1 ≤ Z → natural-number subtraction with m ≥ 1; reason: m is a positive integer, so it agrees with the source
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 20 (PDF 23), Lemma 3.5, Eq. (3.20)

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Stream
import Definitions.Def_SpanForestStream_Unrestricted_Transducer

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Lemma 3.5 (exact single-row interface): there are absolute `β₀, C₀, c > 0` such that for every
integer `Z ≥ 0`, every `0 < η < β₀/2` with `L_η = ln(1/(2η))`, and positive integers `N, U, m` with
`m ≥ L_η`, `U ≥ C₀ m`, `N + U ≤ v`, `m − 1 ≤ Z`, every algorithm with error at most `η` on all legal
streams with at most `Z` deletion operations has, in both peak-space measures,
`s + 1 ≥ c N L_η log₂(2 + m/L_η) log₂(U/m)`. -/
theorem lemma_3_5 :
    ∃ β₀ C₀ c : ℝ, 0 < β₀ ∧ 0 < C₀ ∧ 0 < c ∧
      ∀ (v Z : ℕ) (η : ℝ) (N U m : ℕ), 0 < η → η < β₀ / 2 → 0 < N → 0 < U → 0 < m →
        Real.log (1 / (2 * η)) ≤ m → C₀ * m ≤ U → N + U ≤ v → m - 1 ≤ Z →
        ∀ A : Transducer v,
          (∀ w : List (Update v), IsLegal w → numDeletions w ≤ Z →
            A.errorProb w ≤ ENNReal.ofReal η) →
          ENNReal.ofReal (c * N * Real.log (1 / (2 * η)) *
              Real.logb 2 (2 + m / Real.log (1 / (2 * η))) * Real.logb 2 (U / m)) ≤
              A.expPeak + 1 ∧
          ENNReal.ofReal (c * N * Real.log (1 / (2 * η)) *
              Real.logb 2 (2 + m / Real.log (1 / (2 * η))) * Real.logb 2 (U / m)) ≤
              A.hardPeak + 1 := by sorry

end SpanForestStream.Unrestricted
