-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_Supplement_lemma_B_1
-- name    : SublinearChoresMMS.Disposal.Supplement.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:03:57.00733+00:00
-- url     : https://prove2.me/theorems/b5305a82-90ec-4355-b15d-1a8758d43bad
-- title:
--   Lemma B.1 — pack all representatives with few changes
-- statement:
--   There exist absolute constants $C_5,A>0$ and an integer $n_0\ge2$, chosen before all instance data, with the following property. For every $n\ge n_0$ and $1\le k<n$, the Appendix B block size $q=\lfloor(n^2/\log n)^{1/3}\rfloor$ is positive. Let $q\mid m$ and let nonnegative costs be weakly decreasing in the common order. Suppose that for each agent there is an actual partition of $M$ into $n-k+1$ bundles of cost at most one. Put $L=\lceil(n-k)/q+C_5\log n\rceil$. For every agent there is a packing $p$ of all representatives, including the first, with
--
--   $$\sum_{r:p(r)=t}c_i(\widehat e_r)\le1\quad(t\in[L]),\qquad\#\{r\ge2:p(r)\ne p(r-1)\}\le A L^2.$$
--
--   No representative is excluded. Empty representative sequences have zero changes. This is the complete-coverage segmented packing used by both Appendix B companion constructions.
--
--   Differences from the source:
--   - generalization: the strictly positive distinct ordered proof regime inherited from Section 2 → nonnegative weakly ordered costs with an actual (n-k+1)-part partition of costs at most one; reason: the B.1 packing proof uses only weak order, nonnegativity and that partition; it includes the source regime and also ties, zero costs and empty chores
--   - encoding: all representatives packed into L bins with O(L^2) assignment changes → a total map Fin(m/q) to Fin L, unit-load conclusions and one absolute change constant before n, k, m and costs; reason: no representative, including the first, can be excluded; the change count is adjacent label changes rather than the base excluded-first segment count
--   - encoding: finite agents, chores, complete partitions and finite lotteries → zero-based Fin labels, owner maps and published finite real-weight laws with positive-weight support; reason: bijections cover exactly the finite source instances, and repeated lottery atoms can be merged
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma B.1, printed p. 29 / PDF p. 30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Supplement_AppendixPacking

namespace SublinearChoresMMS.Disposal.Supplement

/-- Lemma B.1, printed 29 / PDF 30, with the actual (n-k+1)-part partition
assumption of B.1, printed 28 / PDF 29. No representative is excluded. -/
theorem lemma_B_1 :
    ∃ C₅ A : ℝ, 0 < C₅ ∧ 0 < A ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
        0 < appendixBlockSize n ∧
        ∀ m : ℕ, appendixBlockSize n ∣ m → ∀ c : Cost n m,
          Nonnegative c → IDO c →
          (∀ i : Fin n, ∃ X : Allocation (n - k + 1) m,
            ∀ j, cost c i (bundle X j) ≤ 1) →
          ∀ i : Fin n,
            ∃ p : AllPacking m (appendixBlockSize n) (appendixBinCount C₅ n k),
              (∀ t, allBinLoad c i p t ≤ 1) ∧
              (labelChanges p : ℝ) ≤ A * (appendixBinCount C₅ n k : ℝ) ^ 2 := by sorry

end SublinearChoresMMS.Disposal.Supplement
