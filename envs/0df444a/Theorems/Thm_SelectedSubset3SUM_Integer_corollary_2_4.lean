-- Prove2me | Theorems.Thm_SelectedSubset3SUM_Integer_corollary_2_4
-- name    : SelectedSubset3SUM.Integer.corollary_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:30.149668+00:00
-- url     : https://prove2.me/theorems/a6186234-e10f-46a0-9690-9f6c078ff186
-- title:
--   Corollary 2.4 — unbalanced all-numbers integer 3SUM in the exact three-term time
-- statement:
--   For every fixed natural exponent $\kappa$, there is a single finite randomized word-RAM program that handles arbitrary finite $A,B,C\subseteq[N^\kappa]$, where $N=|A|+|B|$ and $\widehat n=\sqrt{|A||B|}$. It returns a Boolean for each $c\in C$, true exactly when $c\in A+B$, except on a joint failure event of probability $O(1/N)$. When both summand sets are nonempty, its worst-case total running time is
--
--   $$O\!\left(\widehat n^{393/200}+N\widehat n^{899/1000}+|C|\widehat n^{193/200}\right).$$
--
--   The program, word factor, positive runtime/error constant and size-dependent time budget precede the input instance. The formula is a genuine O bound with the exact source exponents, without a hidden polylogarithm or balance assumption. A side may remain a singleton as the other grows, and $|C|$ remains independent of the side sizes. If a side is empty, all outputs are exactly false, on every tape, with linear input/output time. Empty query lists are allowed. The error event covers the whole answer vector and any rejected run, and every random tape must halt within budget.
--
--   This is the paper's full batch membership result, including all preprocessing, prime and coin operations, sorting and output costs.
--
--   Differences from the source:
--   - encoding: finite sets and set families → arbitrary-order duplicate-free lists, with subset masks on Fin d; reason: every finite-set instance has such a presentation; no sorting or disjointness promise is added and all presentation and output costs are charged
--   - encoding: Monte Carlo total time and O(1/N) error → one finite fair-bit program for each fixed magnitude exponent, a size-dependent worst-case budget, and a measurable event that any Boolean output is incorrect or the run rejects; reason: the source allows truncation and amplification; every tape must halt and the joint event includes all queries, with actual sampling, preprocessing and output writes charged
--   - encoding: asymptotic three-term cost in the positive-product regime → the same exact exponents for every positive product, exact answers with linear input/output time when a side is empty, and K/max(1,N) as a total error bound; reason: the positive-size expression cannot pay for output when nhat=0; these explicit base cases give its ordinary algorithmic boundary convention without excluding any imbalanced family
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Corollary 2.4, p.9; worst-case Monte Carlo convention, p.8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Definitions.Def_SelectedSubset3SUM_Integer_AllQueries

namespace SelectedSubset3SUM.Integer

/-- Corollary 2.4, p.9: all-query unbalanced integer 3SUM, exact source exponents.
Empty sides have exact answers and a linear input/output budget. Every positive product,
including an indefinitely singleton side, uses the advertised three-term O bound. -/
theorem corollary_2_4 :
    ∀ κ : ℕ, ∃ (code : List TrulySubcubicAPSP.Instr) (b : ℕ) (K : ℝ)
      (T : ℕ → ℕ → ℕ → ℕ),
      0 < b ∧ 0 < K ∧
      ∀ I : SumInput, I.Valid κ →
        (sumCharge 0 (T I.A.length I.B.length I.C.length) I : ℝ) ≤
          K * corollaryCost I.A.length I.B.length I.C.length ∧
        ∀ W ≥ b * (Nat.log2 (max 2 I.N) + 1),
          MonteCarloAt code W 0 (T I.A.length I.B.length I.C.length) K I := by sorry

end SelectedSubset3SUM.Integer
