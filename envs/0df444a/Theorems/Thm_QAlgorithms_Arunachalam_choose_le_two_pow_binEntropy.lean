-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_choose_le_two_pow_binEntropy
-- name    : QAlgorithms.Arunachalam.choose_le_two_pow_binEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:06.855847+00:00
-- url     : https://prove2.me/theorems/3631316a-0685-4973-a583-84f936bcf3e0
-- title:
--   Binomial coefficients and their partial sums are at most 2^{nH(·/n)}
-- statement:
--   Let $H$ be the binary entropy in bits and let $n$ be a positive integer. Then
--
--   1. $\binom nk\le 2^{nH(k/n)}$ for every integer $0\le k\le n$;
--   2. $$
--   \sum_{i=0}^m\binom ni\le 2^{nH(m/n)}\quad\text{for every integer } 0\le m\le n/2.
--   $$
--
--   The second bound counts the strings in a Hamming ball and is used to bound conditional entropies in the information-theoretic lower bounds.
--
--   **Formalization Note** The condition $m\le n/2$ is written $2m\le n$ to avoid natural-number division.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 162, Fact 7.3.8. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
set_option autoImplicit false

namespace QAlgorithms.Arunachalam





/-- Arunachalam p.162, Fact 7.3.8: for every positive integer `n`, `binom(n, k) ≤ 2^{n H(k/n)}`
for all `k ≤ n`, and `∑_{i=0}^{m} binom(n, i) ≤ 2^{n H(m/n)}` for all `m ≤ n/2` (`H` the binary
entropy in bits). -/
theorem choose_le_two_pow_binEntropy {n : ℕ} (hn : 1 ≤ n) :
    (∀ k : ℕ, k ≤ n →
        ((n.choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((k : ℝ) / (n : ℝ)))) ∧
      ∀ m : ℕ, 2 * m ≤ n →
        ∑ i ∈ Finset.range (m + 1), ((n.choose i : ℕ) : ℝ) ≤
          (2 : ℝ) ^ ((n : ℝ) * binEntropy2 ((m : ℝ) / (n : ℝ))) := by
  sorry


end QAlgorithms.Arunachalam
