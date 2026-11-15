-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_Supplement_theorem_4
-- name    : StreamTesting.Bipartiteness.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:02:35.013463+00:00
-- url     : https://prove2.me/theorems/eae6df05-39ca-4eee-9fbb-de07dbfa688a
-- title:
--   Theorem 4 — worst-order triangle-freeness testing
-- statement:
--   There is an absolute $C>0$ such that for every $n,d\ge1$ and $0<\varepsilon\le1$, one randomized forward-only full-neighborhood tester satisfies
--
--   $$q\le\lceil Cd/\varepsilon\rceil.$$
--
--   At every fixed order of every simple $n$-vertex graph of maximum degree at most $d$, it accepts triangle-free inputs and rejects inputs requiring at least $\varepsilon dn$ deletions, in each case with probability at least $2/3$. The cap holds on all degree-bounded inputs and all positive-probability private choices. The tester is selected before the hidden input. This gives the source's constant-in-$n$ worst-order upper bound.
--
--   Differences from the source:
--   - encoding: arbitrary randomized forward-only graph algorithms on n observed labels → input-independent PMFs over the published history policies on Fin n, with actual execution; reason: for fixed n all graph-observation histories are finite, so every private random tape induces such a distribution without a memory or computation bound
--   - encoding: O(d/epsilon) queries with success at least 2/3 → one absolute C before n,d,epsilon and a natural ceiling on the worst-run cap; reason: the proof on p.12 truncates after 100 times the expected cost, losing at most 0.01 success; a full-input branch handles small n
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 4, printed p.11 / PDF p.11.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_TriangleFarness
import Definitions.Def_StreamTesting_Bipartiteness_Supplement_GraphTesting
import Definitions.Def_StreamTesting_Bipartiteness_QueryCap

namespace StreamTesting.Bipartiteness.Supplement

/-- Theorem 4, p.11: one absolute constant, all positive sizes and parameters. -/
theorem theorem_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 1 ≤ n → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ μ : RandomPolicy n,
        QueryCap d μ ⌈C * (d : ℝ) / ε⌉₊ ∧
        WorstOrderTester (fun G => G.CliqueFree 3) (fun G => TriangleFar G d ε) d μ := by sorry

end StreamTesting.Bipartiteness.Supplement
