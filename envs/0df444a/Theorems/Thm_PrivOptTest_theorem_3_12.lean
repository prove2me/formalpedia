-- Prove2me | Theorems.Thm_PrivOptTest_theorem_3_12
-- name    : PrivOptTest.theorem_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:31.853211+00:00
-- url     : https://prove2.me/theorems/392e6ae8-6d37-44a4-ae24-ff5ffb434067
-- title:
--   Theorem 3.12, p.21 — upper bound for thresholds (corrected: log = log₂)
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $\mathcal X\subset\mathbb R$ be finite with $|\mathcal X|=m\ge4$, let $\varepsilon\in(0,1]$, $\beta\in(0,1/3]$ and $1\le t\le n$ with
--   $$t\ge C\,\frac{\log\log m}{\varepsilon}\Big(\log\frac1\beta+\log\frac{\log\log m}{\varepsilon}\Big),$$
--   logarithms to base 2. Then Algorithm 2, run on the ranks of the records with the lifting and the blocks of size $\lfloor t/2\rfloor$ of Lemma 3.5 and Remark 3.6, is an $\varepsilon$-private tester for $\mathcal H_{\mathrm{thr}}$ with resolution $t$ and failure probability at most $\beta$.
--
--   This is the upper half of Theorem 1.3: resolution $\tilde O(\log\log m/\varepsilon)$, independent of $n$.
--
--   Differences from the source:
--   - correction: log → log₂; reason: under natural logarithms the statement is false: at m = 4, ε = 1, β = 1/3 the right-hand side is negative (ln ln 4 ≈ 0.327), so t = n = 2 is allowed, k = 1, and Algorithm 2 outputs Far on a Match input with probability ≥ 0.47 > 1/3; log₂ is the paper’s convention in §E and in T = ⌈log₂ b⌉
--   - encoding: the hypothesis n ≥ C (log log m/ε) log(log log m/(βε)) → omitted; reason: under log₂, log(1/β) + log(L/ε) = log(L/(βε)), so it follows from n ≥ t and the first hypothesis
--   - reading: A_val-thr on S_A, S_B ∈ ({0,1}^b)^n → avalThr: ranks in {0,1}^⌈log₂ m⌉, lifted by ψ_A, ψ_B, blocks of k = ⌊t/2⌋ records, Algorithm 2 with b = ⌈log₂ m⌉ + 1 and n := k; reason: §1.4.2 (p.9), Lemma 3.5 and Remark 3.6 (p.16); the promise holds only on the blocks
--   - encoding: multisets over X → sequences Fin n → X; reason: neighbours replace one record; the protocol depends on the inputs only through sorted blocks
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 3.12, p.21; Algorithm 2, p.20; Lemma 3.5 and Remark 3.6, p.16

import Mathlib
import Definitions.Def_PrivOptTest_IsTester
import Definitions.Def_PrivOptTest_algo2

namespace PrivOptTest

/-- **Theorem 3.12** (Upper bound for thresholds, p.21; corrected: `log = log₂`). There is a universal
`C > 0` such that for every finite `X ⊂ ℝ` with `|X| = m ≥ 4`, every `n`, `ε ∈ (0, 1]`, `β ∈ (0, 1/3]`
and `t ∈ [n]` with `t ≥ C (log log m/ε)(log(1/β) + log(log log m/ε))`, Algorithm 2 is an ε-private
tester for `H_thr` with resolution `t` and failure probability at most `β`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 3.12, p.21; Algorithm 2, p.20; Lemma 3.5 and Remark 3.6, p.16.

**Formalization Note.** `log` is `log₂`: with natural logarithms the statement is false (at `m = 4`,
`ε = 1`, `β = 1/3` the hypothesis allows `t = n = 2`, and then Algorithm 2 errs on a Match input with
probability above `1/3`). The paper's second hypothesis `n ≥ C (log log m/ε) log(log log m/(βε))` is
implied by the first and `n ≥ t` under `log₂`, so it is omitted. Algorithm 2 is run as the paper runs
it (`avalThr`): records are ranks in `X`, lifted by `ψ_A`, `ψ_B`, each party keeps its block of
`k = ⌊t/2⌋` records, and the algorithm's `n` is `k`. Inputs are sequences `Fin n → X`. -/
theorem theorem_3_12 :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset ℝ) (n t : ℕ) (ε β : ℝ), 4 ≤ X.card → 1 ≤ t → t ≤ n →
      0 < ε → ε ≤ 1 → 0 < β → β ≤ 1 / 3 →
      C * (Real.logb 2 (Real.logb 2 X.card) / ε) *
          (Real.logb 2 (1 / β) + Real.logb 2 (Real.logb 2 X.card / ε)) ≤ t →
      IsTester (avalThr X n t ε β) (HthrOn X) ε t β := by sorry

end PrivOptTest
