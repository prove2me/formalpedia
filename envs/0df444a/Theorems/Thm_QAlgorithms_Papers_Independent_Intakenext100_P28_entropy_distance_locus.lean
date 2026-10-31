-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_entropy_distance_locus
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.entropy_distance_locus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:53:10.983634+00:00
-- url     : https://prove2.me/theorems/c1e5916f-d5e1-49c3-93ec-01a3fb8b0b2c
-- title:
--   Theorem 29: Exact entropy–distance locus: maximum entropy at TV=Delta is log M-min_m d(m/M+Delta/2||m/M); minimum TV at a fixed entropy in [h_(k-1),h_k) is 2(1-(k+theta)/M), with explicit attaining la
-- statement:
--   Let $M>1$ be an integer and $U$ uniform on $M$ symbols. For $0<\Delta\le2(1-1/M)$,
--
--   $$\max_{|P-U|=\Delta}H(P)=\log_bM-
--   \min_{1\le m\le M-\lceil\Delta M/2\rceil}d(m/M+\Delta/2\|m/M).$$
--
--   For a minimizing $m$, the maximizing law has $m$ masses $1/M+\Delta/(2m)$ and the remaining masses $1/M-\Delta/[2(M-m)]$. Define $h_0=0$, $h_{M-1}=\log_bM$, and $h_k=h(k/M)+(k/M)\log_bk$ for $1\le k\le M-2$, where $h$ is binary entropy. If $H\in[h_{k-1},h_k)$, $1\le k\le M-1$, then
--
--   $$\min_{H(P)=H}|P-U|=2(1-(k+\theta)/M).$$
--
--   Here $0\le\theta<1$ is chosen so the attaining law has entropy $H$: its masses are $1-(k-1+\theta)/M$, then $k-1$ masses $1/M$, then $\theta/M$, then zeros. The statement includes existence of all optimizing parameters and attaining laws, covering (376)–(381). The excluded endpoint $H=\log_bM$ is realized by the uniform law with distance zero.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 52, Theorem 29

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 29: Exact shannonEntropyBase–distance locus: maximum shannonEntropyBase at TV=Delta is log M-min_m d(m/M+Delta/2||m/M); minimum TV at a fixed shannonEntropyBase in [h_(k-1),h_k) is 2(1-(k+theta)/M), with explicit attaining laws. Sason--Verdu, arXiv:1508.00335v7, PDF p.52.  -/
theorem entropy_distance_locus
    (b : LogBase) (n : ℕ) (hn : 1 < n) :
    (∀ d : ℝ, 0 < d → d ≤ 2 * (1 - 1 / (n : ℝ)) →
      ∃ m : ℕ, 1 ≤ m ∧ m ≤ n - ⌈d * n / 2⌉₊ ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ n - ⌈d * n / 2⌉₊ →
          binaryKL b ((m : ℝ) / n + d / 2) ((m : ℝ) / n) ≤
            binaryKL b ((j : ℝ) / n + d / 2) ((j : ℝ) / n)) ∧
        FiniteProbabilityLaw (entropyMaxLaw n m d) ∧ finiteTV (entropyMaxLaw n m d) (uniformLaw n) = d ∧
        shannonEntropyBase b (entropyMaxLaw n m d) = logB b n - binaryKL b ((m : ℝ) / n + d / 2) ((m : ℝ) / n) ∧
        (∀ p : Fin n → ℝ, FiniteProbabilityLaw p → finiteTV p (uniformLaw n) = d →
          shannonEntropyBase b p ≤ shannonEntropyBase b (entropyMaxLaw n m d))) ∧
    (∀ (k : ℕ) (H : ℝ), 1 ≤ k → k ≤ n - 1 →
      uniformEntropyThreshold b n (k - 1) ≤ H → H < uniformEntropyThreshold b n k →
      ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ FiniteProbabilityLaw (entropyMinLaw n k t) ∧
        shannonEntropyBase b (entropyMinLaw n k t) = H ∧
        finiteTV (entropyMinLaw n k t) (uniformLaw n) = 2 * (1 - ((k : ℝ) + t) / n) ∧
        (∀ p : Fin n → ℝ, FiniteProbabilityLaw p → shannonEntropyBase b p = H →
          2 * (1 - ((k : ℝ) + t) / n) ≤ finiteTV p (uniformLaw n))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
