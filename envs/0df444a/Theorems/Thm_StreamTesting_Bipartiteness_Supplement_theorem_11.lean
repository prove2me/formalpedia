-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_Supplement_theorem_11
-- name    : StreamTesting.Bipartiteness.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:04:19.260148+00:00
-- url     : https://prove2.me/theorems/5bbad468-8c03-4c9b-b5c8-265d3dbbfe8c
-- title:
--   Theorem 11 — distinguishing one cycle from six-cycles
-- statement:
--   There are absolute $c>0$ and $N\ge12$ such that for every $n\ge N$ divisible by six, every randomized forward-only algorithm distinguishing every labeled $C_n$ from every labeled disjoint union of $n/6$ copies of $C_6$, with success at least $2/3$ for each fixed arrival order, requires
--
--   $$q\ge c\sqrt n.$$
--
--   Here $q$ is a worst-run query cap on the promised inputs and every order; no cap on off-promise inputs is assumed. There is no free-endpoint side information. Arbitrary randomized history-dependent policies are quantified after the uniform constants. This is the source's full promise lower bound.
--
--   Differences from the source:
--   - encoding: arbitrary randomized forward-only graph algorithms on n observed labels → input-independent PMFs over the published history policies on Fin n, with actual execution; reason: for fixed n all graph-observation histories are finite, so every private random tape induces such a distribution without a memory or computation bound
--   - encoding: n sufficiently large and divisible by 6; all labeled cycle instances → N >= 12, 6 divides n, and graph isomorphisms from the ordinary cycle and n/6 disjoint six-cycles; reason: these are exactly the preceding paragraph assumptions and all relabelings; the two cases are disjoint in this regime
--   - encoding: Omega(sqrt(n)) worst-case queries on the distinguishing task → positive c and eventual threshold before the algorithm, with a cap only on the promise; reason: the resource quantifier does not add a requirement on off-promise graphs
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 11, printed p.15 / PDF p.15.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_CycleDistinguishing
import Definitions.Def_StreamTesting_Bipartiteness_Supplement_PromiseCap

namespace StreamTesting.Bipartiteness.Supplement

/-- Theorem 11, p.15: every labeling and order, promise-restricted cap. -/
theorem theorem_11 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 12 ≤ N ∧ ∀ n : ℕ, N ≤ n → 6 ∣ n →
      ∀ (μ : RandomPolicy n) (q : ℕ), PromiseQueryCap CyclePromise μ q →
        CycleDistinguisher μ → c * Real.sqrt (n : ℝ) ≤ (q : ℝ) := by sorry

end StreamTesting.Bipartiteness.Supplement
