-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_Supplement_theorem_7
-- name    : StreamTesting.Bipartiteness.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:03:50.951561+00:00
-- url     : https://prove2.me/theorems/2be0ac8f-85cf-4ade-a129-9a78ff8f6646
-- title:
--   Theorem 7 — worst-order connectivity query lower bound
-- statement:
--   There are absolute $c>0$ and $N\ge12$ such that, for every degree bound $d\ge2$, every $0<\varepsilon\le1/(12d)$, and every $n\ge N$, every randomized worst-order connectivity tester with success at least $2/3$ satisfies
--
--   $$q\ge c\sqrt n$$
--
--   whenever $q$ caps its queries on all degree-bounded inputs, all orders and all positive-probability private choices. The source's explicit constant setting is $d=2$, $\varepsilon=1/24$, already using only degree-two hard graphs. The conclusion is eventual in every input size, without a divisibility restriction, cycle promise, or bounded-memory assumption. It is the full asymptotic worst-order connectivity lower bound.
--
--   Differences from the source:
--   - encoding: arbitrary randomized forward-only graph algorithms on n observed labels → input-independent PMFs over the published history policies on Fin n, with actual execution; reason: for fixed n all graph-observation histories are finite, so every private random tape induces such a distribution without a memory or computation bound
--   - generalization: Omega(sqrt(n)) connectivity lower bound, already at maximum degree two with epsilon0 = 1/24 → one uniform lower bound for every d >= 2 and 0 < epsilon <= 1/(12d); reason: the same degree-two hard graphs need at least their number of components minus one new edges, irrespective of the permitted final degree; d=2 and epsilon=1/24 recover the source explicit setting
--   - encoding: Omega(sqrt(n)) in the worst case → absolute c>0 and an eventual threshold N before all sizes and policies; reason: this expands the asymptotic quantifiers; unlike Theorem 11 no divisibility restriction is imposed, so bounded-residue sizes are part of the required proof
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 7, printed p.13 / PDF p.13.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_ConnectivityFarness
import Definitions.Def_StreamTesting_Bipartiteness_Supplement_GraphTesting
import Definitions.Def_StreamTesting_Bipartiteness_QueryCap

namespace StreamTesting.Bipartiteness.Supplement

/-- Theorem 7, p.13: all sufficiently large sizes, with no divisibility promise. -/
theorem theorem_7 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 12 ≤ N ∧
      ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (12 * (d : ℝ)) →
      ∀ n : ℕ, N ≤ n → ∀ (μ : RandomPolicy n) (q : ℕ),
        QueryCap d μ q →
        WorstOrderTester (fun G => G.Connected) (fun G => ConnectivityFar G d ε) d μ →
        c * Real.sqrt (n : ℝ) ≤ (q : ℝ) := by sorry

end StreamTesting.Bipartiteness.Supplement
