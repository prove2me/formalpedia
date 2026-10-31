-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P44_lemma4_10B
-- name    : QAlgorithms.Papers.Independent.Intake100.P44.lemma4_10B
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:28:23.417508+00:00
-- url     : https://prove2.me/theorems/1bdd2e44-e668-4d98-91bc-ff7ec2ff7111
-- title:
--   Finite positive ell-one disjointness selection with explicit cardinality
-- statement:
--   Let $k\ge0$ be an integer and $\varepsilon>0$. Set
--
--   $$
--   \ell=\lfloor1/\varepsilon\rfloor+1,\qquad N=k^\ell.
--   $$
--
--   Then $N\ge k$. Given any nonnegative real array $(f_i(j))_{i,j=1}^{N}$ such that $\sum_{j=1}^{N}f_i(j)\le1$ for every $i$, there exist $1\le n_1<\cdots<n_k\le N$ such that
--
--   $$
--   \sum_{\substack{1\le r\le k\\r\ne i}} f_{n_i}(n_r)<\varepsilon\qquad(1\le i\le k).
--   $$
--
--   The rows are exactly elements of the positive unit ball of $\ell_1^N$. The off-diagonal sum involves only selected indices. This finite selection result supplies the elementary disjointness step for the paper's predual arguments. At $k=0$ the selection is empty.
-- source:
--   Banach embedding properties of non-commutative L^p-spaces, arXiv:math/0005150v1, PDF p. 30, Lemma 4.10 B and explicit bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P44

noncomputable section

open scoped BigOperators ENNReal

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Next46.P30 (intervalMeasure)

namespace QAlgorithms.Papers.Independent.Intake100.P44

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Lemma 4.10B, with its explicit bound, PDF pp.30–31. A nonnegative real
N by N array with row sums at most one is exactly an N-tuple in the positive
unit ball of ell_1^N. Off-diagonal sums use the selected k coordinates only. -/
theorem lemma4_10B (k : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, N = finiteDisjointnessBound k eps ∧ k ≤ N ∧
      ∀ f : Fin N → Fin N → ℝ,
        (∀ i j, 0 ≤ f i j) → (∀ i, ∑ j : Fin N, f i j ≤ 1) →
        ∃ s : Fin k → Fin N, StrictMono s ∧
          ∀ i : Fin k, ∑ r ∈ Finset.univ.erase i, f (s i) (s r) < eps := by sorry

end QAlgorithms.Papers.Independent.Intake100.P44

end
