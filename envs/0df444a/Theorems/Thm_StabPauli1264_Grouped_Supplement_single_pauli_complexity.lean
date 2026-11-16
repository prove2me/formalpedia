-- Prove2me | Theorems.Thm_StabPauli1264_Grouped_Supplement_single_pauli_complexity
-- name    : StabPauli1264.Grouped.Supplement.single_pauli_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:50:50.437207+00:00
-- url     : https://prove2.me/theorems/81c7efcb-62e7-4f59-a5a8-c0bc54701655
-- title:
--   Theorem 2.2 — Single-Pauli learning complexity
-- statement:
--   Fix $0<\varepsilon_0<1/2$ and $0<\delta_0<1/2$. There are constants $c,C>0$ depending only on $\varepsilon_0,\delta_0$ such that for every window $M$, every $0<\varepsilon\le\varepsilon_0$ and every $0<\delta\le\delta_0$,
--
--   $$c\,\frac{r(M)+\ln(1/\delta)}{\varepsilon^2}\;\le\;N_{\mathrm{single}}(M,\varepsilon,\delta)\;\le\;C\,\frac{r(M)+\ln(1/\delta)}{\varepsilon^2}.$$
--
--   $N_{\mathrm{single}}$ is the least number of copies with which one proper learner under random single-Pauli access, not told $p$, $(\varepsilon,\delta)$-learns $M$ under every distribution $p$ and every state; $r(M)$ is the commuting rank. The rank dependence separates single-Pauli access from grouped access (Theorem 2.3).
--
--   Differences from the source:
--   - encoding: N_single as a least integer, and Θ with constants depending only on ε₀, δ₀ → an infimum in ℕ ∪ {∞} compared through the base `countReal`, with ∃ c C > 0 placed after ε₀, δ₀ and before n, m, M, ε, δ; reason: the upper bound forces finiteness; the quantifier order is exactly "depending only on ε₀ and δ₀"
--   - encoding: log → natural logarithm; reason: all logarithms are natural (p. 13)
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Theorem 2.2 and Eq. (6), p. 6; Eq. (3) p. 3; Definition 5.3 p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Supplement_SingleAccess
set_option autoImplicit false

namespace StabPauli1264.Grouped.Supplement

open QAlgorithms.Stabilizer StabPauli1264.Grouped
open scoped BigOperators Classical

/-- Theorem 2.2 (Single-Pauli learning complexity), p. 6: for fixed `ε₀, δ₀ ∈ (0, 1/2)` there are
constants `c, C > 0`, depending only on `ε₀, δ₀` (chosen before the window), such that
`c (r(M) + ln(1/δ))/ε² ≤ N_single(M, ε, δ) ≤ C (r(M) + ln(1/δ))/ε²` for every window,
`0 < ε ≤ ε₀` and `0 < δ ≤ δ₀`. -/
theorem single_pauli_complexity (ε₀ δ₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1 / 2)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1 / 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {n m : ℕ} (M : Window n m) (ε δ : ℝ), 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ δ₀ →
        ENNReal.ofReal (c * ((commutingRank M : ℝ) + Real.log (1 / δ)) / ε ^ 2) ≤
            countReal (singleComplexity M ε δ) ∧
          countReal (singleComplexity M ε δ) ≤
            ENNReal.ofReal (C * ((commutingRank M : ℝ) + Real.log (1 / δ)) / ε ^ 2) := by sorry

end StabPauli1264.Grouped.Supplement
