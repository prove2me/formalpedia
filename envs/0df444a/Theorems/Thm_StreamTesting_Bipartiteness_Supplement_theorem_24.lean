-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_Supplement_theorem_24
-- name    : StreamTesting.Bipartiteness.Supplement.theorem_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:06:12.834754+00:00
-- url     : https://prove2.me/theorems/70e8a974-49c6-46fe-af14-15c4fe95496f
-- title:
--   Theorem 24 — one-sided streaming 132-freeness testing
-- statement:
--   There are absolute $C>0$ and a positive natural exponent $k$ such that, for every $n\ge1$ and $0<\varepsilon\le1$, an input-independent randomized forward-only tester on arbitrary real sequences of length $n$ has worst-run query bound
--
--   $$q\le\left\lceil C\bigl(\varepsilon^{-1}(1+\log n)\bigr)^k\right\rceil.$$
--
--   It accepts every 132-free sequence with probability one and rejects every sequence requiring at least $\varepsilon n$ coordinate changes to become free with probability at least $2/3$. Strict 132 inequalities define the property, so repeated values are included as Remark 25 specifies. The cap holds on every real input and each positive-probability private seed. No hidden structural advice, permutation promise, or power-of-two length restriction is imposed. This supplies the full one-sided polynomial bound of Theorem 24.
--
--   Differences from the source:
--   - encoding: randomized forward-only algorithms on real-valued sequences → actual history-based execution with an unrestricted finite private seed space and zero-based Fin indices; reason: the existence algorithms use finitely many sampling choices at each fixed n and epsilon; their policies still depend on arbitrary observed reals, and no finiteness of real-history policy space is asserted
--   - encoding: (epsilon^-1 log n)^{O(1)} queries → one absolute C>0 and natural k>=1 before n,epsilon, with ceiling of C(epsilon^-1(1+log n))^k; reason: a sufficiently large fixed exponent absorbs the explicit budgets on pp.31–36; n=1 is included by the harmless logarithm shift, and no exponent or epsilon dependence is weakened
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 24, printed p.29 / PDF p.29.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_PatternTester
import Definitions.Def_StreamTesting_Bipartiteness_Supplement_SequenceCap

namespace StreamTesting.Bipartiteness.Supplement

/-- Theorem 24 and Remark 25, p.29: all real sequences, including repeated values. -/
theorem theorem_24 :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, 1 ≤ k ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ A : SeqAlgorithm n Bool,
          SeqQueryCap (fun _ => True) A
            ⌈C * (ε⁻¹ * (1 + Real.log (n : ℝ))) ^ k⌉₊ ∧
          OneSided132Tester ε A := by sorry

end StreamTesting.Bipartiteness.Supplement
