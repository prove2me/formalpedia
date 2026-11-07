-- Prove2me | Theorems.Thm_QuasiPolyTrace_lemma_43
-- name    : QuasiPolyTrace.lemma_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:37.171501+00:00
-- url     : https://prove2.me/theorems/13817470-d353-40ac-b49b-eed3c5a81f02
-- title:
--   Lemma 43 — base case: a mean-based discrepancy near the first discrepancy
-- statement:
--   There are constants $C^*>0$ and $D_0$ such that the following holds, with strings and traces indexed from $0$. Let $x,y\in\{0,1\}^n$ have first discrepancy $d=\min\{i:x_i\ne y_i\}\ge D_0$ and let $p\in[8d^{-1/2},\tfrac12]$. Writing $\tilde a_j=\mathbb E_{U\sim\mathrm{Del}_p(x)}[U_j]-\mathbb E_{U\sim\mathrm{Del}_p(y)}[U_j]$, there is $j\le pd+C^*p^{1/3}d^{2/3}$ with
--
--   $$
--   |\tilde a_j|\ \ge\ \exp\big(-C^*d^{1/3}p^{-1/3}\big).
--   $$
--
--   The induction of Theorem 44 starts from this order-one statistic.
--
--   Differences from the source:
--   - encoding: 0-based d and U_j (§8.1) → IsFirstDiscrepancy x y (d + 1) and E[U_j] = stat p x {j + 1}; reason: the Lean predicate and statistic are 1-based; the shift by one is exact
--   - reading: for some fixed constant C* > 0 … for d larger than some fixed constant → ∃ C* > 0, ∃ D₀, chosen before n, x, y, p; reason: both constants are "fixed", i.e. universal
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 43, p.40 (0-based indexing, §8.1 preamble, p.40)

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_QuasiPolyTrace_stat
import Definitions.Def_QuasiPolyTrace_IsFirstDiscrepancy

namespace QuasiPolyTrace

open OAI.TraceReconstruction

/-- **Lemma 43 (base case: a mean-based discrepancy near the first discrepancy).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 43,
p.40: "Let x, y ∈ {0, 1}^n be two strings with d = min{i : x_i ≠ y_i}. Let p ∈ [8d^{−1/2}, ½]. Define
ã_i := E_{U∼Del_p(x)}[U_i] − E_{U∼Del_p(y)}[U_i]. For some fixed constant C∗ > 0, there exists
j ≤ pd + C∗p^{1/3}d^{2/3} such that |ã_j| ≥ exp(−C∗d^{1/3}p^{−1/3}), for d larger than some fixed
constant." Subsection preamble (p.40): "In this subsection we index x starting at 0, i.e.,
x = x_0x_1 … x_{n−1}."

**Formalization Note.**
* Indices are 0-based, as in §8.1: `d` is the 0-based index of the first discrepancy, i.e. the 1-based
  first discrepancy is `d + 1` (`IsFirstDiscrepancy x y (d + 1)`), and `U_j` is the bit of the trace at
  0-based position `j`, so `E[U_j] = stat p x {j + 1}` (1-based statistic of order 1).
* "For some fixed constant C∗ > 0 … for d larger than some fixed constant": `C∗` and the threshold `D₀`
  are universal, chosen before the strings and `p`.
* Positions `j` are natural numbers. -/
theorem lemma_43 :
    ∃ Cs D₀ : ℝ, 0 < Cs ∧ ∀ (n : ℕ) (x y : Word n) (d : ℕ), IsFirstDiscrepancy x y (d + 1) →
      D₀ ≤ d → ∀ p : ℝ, 8 * (d : ℝ) ^ (-(1 / 2 : ℝ)) ≤ p → p ≤ 1 / 2 →
      ∃ j : ℕ, (j : ℝ) ≤ p * d + Cs * p ^ (1 / 3 : ℝ) * (d : ℝ) ^ (2 / 3 : ℝ) ∧
        Real.exp (-(Cs * (d : ℝ) ^ (1 / 3 : ℝ) * p ^ (-(1 / 3 : ℝ)))) ≤
          |stat p (List.ofFn x) {(j : ℤ) + 1} - stat p (List.ofFn y) {(j : ℤ) + 1}| := by sorry

end QuasiPolyTrace
