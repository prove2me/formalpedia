-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_theorem_14
-- name    : StreamTesting.Bipartiteness.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:59:54.535195+00:00
-- url     : https://prove2.me/theorems/a40167a5-8e9c-4c38-803e-02c95c2d61bb
-- title:
--   Theorem 14 — nearly linear worst-case queries for random-order bipartiteness testing
-- statement:
--   There are a natural degree $d\ge3$, constants $\varepsilon_0,C>0$, a sufficiently large threshold $N_0$, and arbitrarily large integers $n\ge N_0$ with $\log\log n>0$ such that every randomized forward-only neighborhood-query algorithm that tests bipartiteness on every simple $n$-vertex graph of maximum degree at most $d$, with farness parameter $\varepsilon_0$ and success probability at least $2/3$, satisfies
--
--   $$q\ge n^{1-C/\log\log n}$$
--
--   whenever $q$ bounds its queries in the worst case over all inputs, arrival permutations, and positive-probability internal choices. Correctness is averaged over a uniformly random arrival order and independent private coins. Constants and witness sizes are chosen before the tester; the family of sizes is unbounded. There is no memory or computation bound and no restriction to nonadaptive policies, special input families, or forest transcripts. This is the source’s full $n^{1-O(1/\log\log n)}$ lower bound.
--
--   Differences from the source:
--   - encoding: finite simple graphs on n observed labels → SimpleGraph (Fin n) with the same n labels and arrival permutations; reason: zero-based relabeling preserves every input graph and full-neighborhood query; the goal places no parity or hard-family restriction on n
--   - encoding: arbitrary randomized forward-only neighborhood-query algorithms → input-independent PMFs on all deterministic observed-history tables with actual recursive execution; reason: for fixed n the set of observable histories is finite, so any random tape pushes forward to this finite policy space without restricting memory, computation, or private randomness
--   - encoding: infinitely many sizes with n^(1−O(1/log log n)) worst-case queries → uniform d, epsilon0, C>0 and a threshold, followed by arbitrarily large n and then every tester, with q ≥ n^(1−C/log log n); reason: an unbounded subset of the natural numbers is infinite; the proof on p.26 absorbs ceilings and multiplicative factors into C and an eventual threshold
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 14, printed p.20 / PDF p.20; standing model pp.3–4 and §4; proofs pp.25–26 and 40–41.

import Definitions.Def_StreamTesting_Bipartiteness_Tester

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Theorem 14, p.20: uniform constants, unbounded sizes, all randomized testers.
No hard-family, memory, forest, or root-probability promise is imposed on the tester. -/
theorem theorem_14 :
    ∃ d : ℕ, 3 ≤ d ∧ ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
    ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ N₀ ≤ n ∧
      0 < Real.log (Real.log (n : ℝ)) ∧
      ∀ (μ : RandomPolicy n) (q : ℕ), QueryCap d μ q → Tester d ε₀ μ →
        (n : ℝ) ^ (1 - C / Real.log (Real.log (n : ℝ))) ≤ (q : ℝ) := by sorry

end StreamTesting.Bipartiteness
