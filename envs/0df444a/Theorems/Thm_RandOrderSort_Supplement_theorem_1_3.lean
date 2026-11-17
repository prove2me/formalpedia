-- Prove2me | Theorems.Thm_RandOrderSort_Supplement_theorem_1_3
-- name    : RandOrderSort.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:01:23.85528+00:00
-- url     : https://prove2.me/theorems/581dba2c-0ac4-407a-aaf3-8975e477cce9
-- title:
--   Theorem 1.3 — every randomized online algorithm has $\mathrm{cost}<c_0\log n$ with probability at most $4e^{-c_1\sqrt n}$ on i.i.d. $U[0,1]$ inputs
-- statement:
--   There are absolute constants $c_0,c_1>0$ and $n_0$ such that the following holds for every $n\ge n_0$. Let $A$ be any randomized measurable online algorithm with full access to the numerical values that uses exactly $n$ cells (legal on size $n$), with internal random tape $\zeta\sim\mu$. Let $X_1,\dots,X_n$ be independent uniform random variables on $[0,1]$, independent of $\zeta$. Then
--
--   $$\mathbb P_{\zeta,X}\bigl[\mathrm{cost}(A(X_1,\dots,X_n))<c_0\log n\bigr]\le 4e^{-c_1\sqrt n}.$$
--
--   Here $\mathrm{cost}$ is the sum of the absolute differences of adjacent entries of the completed array, and $\log$ is the natural logarithm. The constants do not depend on the algorithm.
--
--   Since the range of uniform inputs is at most $1$, this matches the $O(\log n)$ upper bound of Theorem 1.1: no online algorithm, even randomized and with unlimited memory, achieves cost $o(\log n)$ except with probability exponentially small in $\sqrt n$.
--
--   **Formalization Note** The probability is the product of the tape law and the law of $n$ i.i.d. $U[0,1]$ inputs (the base mission's `iidUnif`). The theorem is universe-polymorphic in the tape space.
--
--   Differences from the source:
--   - encoding: "possibly randomized measurable online algorithm using exactly n cells" → a `RandOnlineAlg` (arbitrary tape space and probability law, full real values, measurable placements) satisfying `LegalOn n` (distinct cells in 0..n−1 for every tape and every input in [0,1]^n); reason: legality is only demanded where the inputs lie, so the class contains every algorithm of the page.
--   - encoding: tape space of arbitrary size → a type in a fixed but arbitrary universe u (the constants are existentially quantified inside each universe instance); reason: Lean cannot quantify over universes; every concrete probability space lives in some universe.
--   - encoding: P[·] on the probability space of (ζ, X) → the product measure μ ⊗ iidUnif n of the possibly non-measurable event, with the bound in ℝ≥0∞; reason: same value on the (measurable) event; for a non-measurable set the outer measure only strengthens the bound.
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Theorem 1.3, p.4; model of the algorithm §5.1, p.40; constants p.42

import Mathlib
import Definitions.Def_RandOrderSort_iidUnif
import Definitions.Def_RandOrderSort_Supplement_RandOnlineAlg

namespace RandOrderSort

namespace Supplement

open MeasureTheory

universe u

/-- **Theorem 1.3 (Lower tail for uniform inputs)**, Kang, Fan, arXiv:2610.15438 (version of
2026-11-01), p.4: "There are absolute constants c0, c1 > 0 and n0 such that, for every n ≥ n0,
every possibly randomized measurable online algorithm A using exactly n cells satisfies
P[cost(A(X1, . . . , Xn)) < c0 log n] ≤ 4e^{−c1√n} on independent U[0, 1] inputs. Its internal
random tape ζ is independent of the input."

**Formalization Note.** The constants are chosen before `n` and the algorithm. The algorithm is a
`RandOnlineAlg` (arbitrary tape space and law, full real values, measurable placements) that is
legal on size `n`. The probability is the product of the tape law and `iidUnif n` (the tape is
independent of the input); `log` is the natural logarithm. -/
theorem theorem_1_3 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : RandOnlineAlg.{u}, A.LegalOn n →
        (A.μ.prod (iidUnif n)) {p : A.Ω × (Fin n → ℝ) | A.cost p.1 p.2 < c₀ * Real.log n} ≤
          ENNReal.ofReal (4 * Real.exp (-(c₁ * Real.sqrt n))) := by sorry

end Supplement

end RandOrderSort
