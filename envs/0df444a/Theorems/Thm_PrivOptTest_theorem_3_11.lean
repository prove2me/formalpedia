-- Prove2me | Theorems.Thm_PrivOptTest_theorem_3_11
-- name    : PrivOptTest.theorem_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:06.421198+00:00
-- url     : https://prove2.me/theorems/1ce2143c-e538-4b17-bc54-605377029936
-- title:
--   Theorem 3.11, p.18 — private common-frequency estimation
-- statement:
--   Let $n,m\ge1$, $\varepsilon>0$ and $\beta\in(0,1)$. Algorithm 1 is a well-formed $\varepsilon$-two-party differentially private protocol, and for every $S_A,S_B\in[m]^n$, with $f=\max_{v\in[m]}\min\{A_v,B_v\}$ and $r=\min\{m,\lceil4n^2/\beta\rceil\}$,
--   $$\Pr\Big[|\hat f-f(S_A,S_B)|\le\frac2\varepsilon\ln\frac{4r}{\beta}\Big]\ge1-\beta,\qquad\Pr\Big[|\hat f-f(S_A,S_B)|\le\frac{2\ln(16n^2/\beta)}{\varepsilon}\Big]\ge1-\beta.$$
--
--   The first bound is the accuracy of each step of the private binary search in Theorem 3.12.
--
--   Differences from the source:
--   - encoding: "Algorithm 1 is an ε-two-party differentially private protocol" → well-formed (measurable, probability coins, terminating) and private in the sense of Definition 2.1; reason: being a protocol of Definition 1.2 includes these conventions
--   - reading: log in the "in particular" display → natural logarithm; reason: the first bound uses ln; with ln the display holds by a sharper union bound, although it is not a substitution in the first bound
--   - encoding: [m] 1-based → Fin m, 0-based; reason: relabelling; same instances
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 3.11 and Algorithm 1, p.18

import Mathlib
import Definitions.Def_PrivOptTest_algo2

open MeasureTheory

namespace PrivOptTest

/-- **Theorem 3.11** (Private Common-Frequency Estimation, p.18). For `n, m ≥ 1`, `ε > 0` and
`β ∈ (0, 1)`, Algorithm 1 is an ε-two-party differentially private protocol, and for every pair of inputs
`S_A, S_B ∈ [m]ⁿ`, with probability at least `1 − β`, `|f̂ − f(S_A, S_B)| ≤ (2/ε) ln(4r/β)` with
`r = min{m, ⌈4n²/β⌉}`; in particular `|f̂ − f(S_A, S_B)| ≤ 2 ln(16n²/β)/ε` with probability at least `1 − β`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 3.11 and Algorithm 1, p.18.

**Formalization Note.** `f = max_{v∈[m]} min{A_v, B_v}` is `commonFreq`; `f̂` is the common output of
`apcf`. Being a protocol includes well-formedness (measurable, probability coins, termination). `log`
is the natural logarithm in both bounds. The "in particular" clause is not a substitution in the first
bound (`r` may be about `4n²/β`), but holds by a sharper union bound. -/
theorem theorem_3_11 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (ε β : ℝ) (hε : 0 < ε) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    (apcf m n ε β).IsWellFormed ∧ (apcf m n ε β).IsPrivate ε ∧
      (∀ SA SB : Fin n → Fin m, ENNReal.ofReal (1 - β) ≤ (apcf m n ε β).outputLaw SA SB
        {o | ∃ y : ℝ, o = Sum.inl y ∧ |y - (commonFreq SA SB : ℝ)| ≤
          2 / ε * Real.log (4 * min (m : ℝ) (⌈4 * (n : ℝ) ^ 2 / β⌉₊ : ℝ) / β)}) ∧
      (∀ SA SB : Fin n → Fin m, ENNReal.ofReal (1 - β) ≤ (apcf m n ε β).outputLaw SA SB
        {o | ∃ y : ℝ, o = Sum.inl y ∧ |y - (commonFreq SA SB : ℝ)| ≤
          2 * Real.log (16 * (n : ℝ) ^ 2 / β) / ε}) := by sorry

end PrivOptTest
