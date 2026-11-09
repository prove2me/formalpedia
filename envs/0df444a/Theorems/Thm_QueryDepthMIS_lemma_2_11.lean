-- Prove2me | Theorems.Thm_QueryDepthMIS_lemma_2_11
-- name    : QueryDepthMIS.lemma_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:36:36.241473+00:00
-- url     : https://prove2.me/theorems/3d7bcbaa-9f65-4b95-9298-e7bf04c8a4c7
-- title:
--   Lemma 2.11 — $\mathbb E[Z(\pi)] \le n + m$
-- statement:
--   Let $G$ be a simple graph with $n$ vertices and $m$ edges. For a uniformly random permutation $\pi$ of $V$, the expected total number of query paths satisfies
--   $$
--   \mathbb E[Z(\pi)] \le n + m,
--   $$
--   where $Z(\pi) = \sum_{v} T(v, \pi)$ and $T(v, \pi)$ is the number of query paths ending at $v$.
--
--   This is the average-case bound of Yoshida, Yamamoto and Ito on the total number of oracle calls; it feeds the few-shortcuts lemma.
--
--   Differences from the source:
--   - encoding: a uniformly random permutation π of V, π(i) the i-th vertex → the uniform (counting) law on orderings ω : V ≃ Fin n, π = ω⁻¹, with 1-based ranks rank ω v = ω v + 1; reason: the same law; positions keep the paper's 1-based values
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 2.11, p.10

import Mathlib
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_QueryDepthMIS_Z
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- Lemma 2.11 ([YYI09]) (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 2.11, p.10): "For a uniformly random permutation π on V,
E[Z(π)] ≤ n + m."

For every simple graph `G` with `n` vertices and `m` edges, the expected total number of query
paths `Z(π) = ∑_v T(v, π)` under a uniformly random permutation is at most `n + m`.

**Formalization Note** `m = |E|` is `G.edgeFinset.card`; `[LinearOrder V]` is the unused
tie-breaker of `RGMISFast.tau`. -/
theorem lemma_2_11 :
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      NoSignalPA.uniformExp (fun ω : Perm V => (Z G (rank ω) : ℝ)) ≤
        (Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ) := by sorry

end QueryDepthMIS
