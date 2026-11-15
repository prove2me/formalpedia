-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_Supplement_theorem_22
-- name    : StreamTesting.Bipartiteness.Supplement.theorem_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:05:16.725215+00:00
-- url     : https://prove2.me/theorems/19264ed6-aea1-4ff0-a6dc-298909689e0d
-- title:
--   Theorem 22 — forward-only common-element search
-- statement:
--   There is an absolute $C>0$ such that, for every $n\ge1$ and $0<\varepsilon\le1$, one input-independent randomized forward-only algorithm on two strictly increasing real lists of length $n$ has worst-run query bound
--
--   $$q\le\lceil C\varepsilon^{-2}(1+\log n)\rceil.$$
--
--   All of the first list arrives before the second. Whenever their common-value set has cardinality at least $\varepsilon n$, the algorithm outputs a value in that set with probability at least $2/3$. The query cap holds for every sorted pair and positive-probability seed, including pairs outside the promise. Values are arbitrary reals; the result neither assumes a bounded range nor grants backward queries. This retains the full parameter dependence in Theorem 22.
--
--   Differences from the source:
--   - encoding: randomized forward-only algorithms on real-valued sequences → actual history-based execution with an unrestricted finite private seed space and zero-based Fin indices; reason: the existence algorithms use finitely many sampling choices at each fixed n and epsilon; their policies still depend on arbitrary observed reals, and no finiteness of real-history policy space is asserted
--   - encoding: O(epsilon^-2 log n) queries → one uniform C and ceiling of C epsilon^-2 (1+log n) for all n>=1; reason: for n>=2 this is the same asymptotic bound, while 1+log n permits the trivial n=1 case; p.29 provides amplification and Markov truncation to a worst-run cap
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 22, printed p.27 / PDF p.27.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_CommonSearch
import Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequenceCap

namespace StreamTesting.Bipartiteness.Supplement

/-- Theorem 22, p.27: the full epsilon^-2 dependence, with the n=1 branch included. -/
theorem theorem_22 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ T : SeqAlgorithm (2 * n) (Option ℝ),
        SeqQueryCap (SortedPairInput n) T
          ⌈C * ε⁻¹ ^ 2 * (1 + Real.log (n : ℝ))⌉₊ ∧
        CommonSearcher n ε T := by sorry

end StreamTesting.Bipartiteness.Supplement
