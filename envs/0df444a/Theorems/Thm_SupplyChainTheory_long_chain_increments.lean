-- Prove2me | Theorems.Thm_SupplyChainTheory_long_chain_increments
-- name    : SupplyChainTheory.long_chain_increments
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:12:26.843872+00:00
-- url     : https://prove2.me/theorems/16879c1e-68e3-4c8c-8209-3a04f86878f8
-- title:
--   Lemma 7.7: building the long chain edge by edge, $[L^n_2] - [L^n_1] \le [L^n_3] - [L^n_2] \le \dots \le [L^n_n] - [L^n_{n-1}] \le [C_n] - [L^n_n]$
-- statement:
--   **Lemma 7.7.** For any balanced system of size $n$ with exchangeable demand, the incremental
--   benefit of each flexible edge added while building the long chain is nondecreasing:
--
--   $$ [L^n_2] - [L^n_1] \;\le\; [L^n_3] - [L^n_2] \;\le\; \cdots \;\le\; [L^n_n] - [L^n_{n-1}] \;\le\; [C_n] - [L^n_n], $$
--
--   where $L^n_k$ is the open chain through products and plants $1, \dots, k$ together with the
--   dedicated edges of the remaining pairs, $L^n_1 = D_n$ and $L^n_n = L_n$. The proof applies
--   Corollary 7.6 to $E = L^n_{k+1}$ with $\alpha = (2, 1)$ and $\beta = (k + 1, k)$: removing
--   $\beta$ gives $L^n_k$, removing $\alpha$ gives $L^n_k$ after moving pair $1$ to the end, which
--   exchangeability allows, and removing both gives $L^n_{k-1}$; the last inequality is the same
--   argument on $C_n$ with $\beta = (1, n)$. The book notes that, unlike Lemma 7.5, this holds only
--   in expectation (Problem 7.15).
--
--   **Formalization Note** The chain of inequalities is stated as its two kinds of link: the
--   consecutive increments for $2 \le k \le n - 1$, and the final link for $n \ge 2$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 250-251, Sect. 7.5.3, Lemma 7.7 and its proof, Eq. (7.29)

import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem long_chain_increments {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {n : ℕ} (S : BalancedSystem P n) :
    (∀ k, 2 ≤ k → k + 1 ≤ n →
        S.expPerf (partialChain n k) - S.expPerf (partialChain n (k - 1))
          ≤ S.expPerf (partialChain n (k + 1)) - S.expPerf (partialChain n k))
      ∧ (2 ≤ n →
        S.expPerf (partialChain n n) - S.expPerf (partialChain n (n - 1))
          ≤ S.expPerf (longChain n) - S.expPerf (partialChain n n)) := by sorry

end SupplyChainTheory
