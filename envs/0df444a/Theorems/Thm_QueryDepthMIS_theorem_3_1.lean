-- Prove2me | Theorems.Thm_QueryDepthMIS_theorem_3_1
-- name    : QueryDepthMIS.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:34:52.004566+00:00
-- url     : https://prove2.me/theorems/7b3b3fa0-7871-402e-892e-6113c7d94d71
-- title:
--   Theorem 3.1 — $\Pr_\pi[\sigma(G) > C\log n] \le 1/n^5$ for every graph on $n$ vertices
-- statement:
--   There is an absolute constant $C$ such that for every simple graph $G$ on $n \ge 2$ vertices and a uniformly random permutation $\pi$ of $V(G)$,
--   $$
--   \Pr_\pi\big[\sigma(G) > C \log n\big] \le \frac{1}{n^5},
--   $$
--   where $\sigma(G)$ is the query depth (the maximum number of vertices of a query path) and $\log$ is the base-2 logarithm.
--
--   Since $\sigma(G)$ is the maximum recursion depth of the recursive randomized greedy MIS oracle over all starting vertices, the oracle has $O(\log n)$ query depth simultaneously for all roots with high probability; the bound is tight up to the constant (Appendix A of the paper).
--
--   Differences from the source:
--   - encoding: a uniformly random permutation π of V, π(i) the i-th vertex → the uniform (counting) law on orderings ω : V ≃ Fin n, π = ω⁻¹, with 1-based ranks rank ω v = ω v + 1; reason: the same law; positions keep the paper's 1-based values
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Theorem 3.1, p.10

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_queryDepth
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- Theorem 3.1 (Upper bound on query depth) (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Theorem 3.1, p.10): "Let G be a simple
undirected graph on n vertices, and let π be a uniformly random permutation of V(G). There is an
absolute constant C such that Pr_π[σ(G) > C log n] ≤ 1/n⁵."

There is a constant `C`, chosen before the graph, such that for every simple graph `G` on
`n ≥ 2` vertices the probability over a uniformly random permutation that the query depth `σ(G)`
(the maximum number of vertices of a query path, Definition 2.6) exceeds `C log₂ n` is at most
`1/n⁵`.

**Formalization Note** The permutation is a uniformly random `ω : V ≃ Fin n` with 1-based ranks
`rank ω`; `σ(G)` is `queryDepth G (rank ω)`; `log` is `Real.logb 2`; `n ≥ 2` is the standing
assumption of §2.1, p.7. `[LinearOrder V]` is the tie-breaker required by `RGMISFast.tau` and is
never used since ranks are injective. -/
theorem theorem_3_1 :
    ∃ C : ℝ, ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      2 ≤ Fintype.card V →
      PunctSketch.coinProb (fun ω : Perm V =>
        C * Real.logb 2 (Fintype.card V) < (queryDepth G (rank ω) : ℝ)) ≤
        1 / (Fintype.card V : ℝ) ^ 5 := by sorry

end QueryDepthMIS
