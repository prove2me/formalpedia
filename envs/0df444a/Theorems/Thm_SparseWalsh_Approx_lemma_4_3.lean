-- Prove2me | Theorems.Thm_SparseWalsh_Approx_lemma_4_3
-- name    : SparseWalsh.Approx.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:03:11.654287+00:00
-- url     : https://prove2.me/theorems/297bc2e9-d57c-4165-a3c9-a71352218580
-- title:
--   Lemma 4.3 — the degree-sensitive frequency locator: O(k log(2d/k)) rows, success at least 7/8
-- statement:
--   There is a universal constant $C$ such that for all integers $1\le k\le d$ there is a probability distribution over binary matrices $A$ with $D\le C\,k\log_2(2d/k)$ rows, each with an associated decoder $\mathrm{Dec}_A$ defined on every bit vector, such that for every fixed $a\in\mathbb F_2^d$ of Hamming weight $|a|\le k$,
--   $$\Pr_A\big[\mathrm{Dec}_A(Aa)=a\big]\ge\frac78.$$
--   This locator is what lets the degree-sensitive algorithms identify a frequency of weight at most $k$ from $O(k\log(2d/k))$ parities instead of $d$ coordinate reads. Appendix C constructs it (the `degLocator` of the definitions).
--
--   Differences from the source:
--
--   - encoding: O(k log(2d/k)) rows → D ≤ C·k·log₂(2d/k) with one universal C chosen before d and k, and the same D for every outcome; reason: explicit constant for the O(·)
--   - encoding: a distribution of binary matrices A with an associated decoder; Dec_A(Aa) = a → a PMF over locators (rows of A with a decoder returning a frequency or failure); dec(meas a) = some a; reason: a total decoder is the special case that never fails, and a decoder that may fail becomes total with the same success probability by outputting any fixed vector on failure
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 18 (PDF p. 21), Lemma 4.3; proof pp. 37-38, App. C.2

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier
import Definitions.Def_SparseWalsh_Approx_Locators

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Lemma 4.3** (Degree-sensitive frequency locator), p. 18 (PDF p. 21). There is one universal
constant `C` such that for every `1 ≤ k ≤ d` there is a law `μ` of locators (a binary matrix `A`
with `D ≤ C·k·log₂(2d/k)` rows, the same `D` for every outcome, together with its decoder) such
that for every fixed `a ∈ F_2^d` with `|a| ≤ k`, `Pr[Dec_A(Aa) = a] ≥ 7/8`. The decoder is defined
on every bit list. -/
theorem lemma_4_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ d k : ℕ, 1 ≤ k → k ≤ d →
      ∃ (D : ℕ) (μ : PMF (Locator d)),
        (D : ℝ) ≤ C * k * Real.logb 2 (2 * d / k) ∧
        (∀ ℓ ∈ μ.support, ℓ.rows.length = D) ∧
        ∀ a : Cube d, weight a ≤ k →
          (7 / 8 : ENNReal) ≤ μ.toOuterMeasure {ℓ | ℓ.dec (meas ℓ a) = some a} := by sorry

end SparseWalsh.Approx
