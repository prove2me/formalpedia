-- Prove2me | Theorems.Thm_QueryDepthMIS_lemma_2_13
-- name    : QueryDepthMIS.lemma_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:50.498203+00:00
-- url     : https://prove2.me/theorems/e119ba31-1bc2-4470-84db-711a52f3398b
-- title:
--   Lemma 2.13 — query-depth division: $\sigma(G_{\mathrm{alive}}(l,r)) \le \sigma(G_{\mathrm{alive}}(l,t)) + \sigma(G_{\mathrm{alive}}(t+1,r)) + 1$
-- statement:
--   Fix a permutation $\pi$ of the vertices of a simple graph $G$ on $n$ vertices. For integers $1 \le l \le t < r \le n$,
--   $$
--   \sigma(G_{\mathrm{alive}}(l, r)) \le \sigma(G_{\mathrm{alive}}(l, t)) + \sigma(G_{\mathrm{alive}}(t + 1, r)) + 1,
--   $$
--   where $\sigma(H)$ is the query depth of the subgraph $H$ with the order inherited from $\pi$.
--
--   The lemma splits the permutation into a prefix and a suffix, so the query depth can be bounded on each part separately.
--
--   Differences from the source:
--   - encoding: a fixed permutation π → every ordering ω : V ≃ Fin n with 1-based ranks; reason: the statement is deterministic
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 2.13, p.10

import Mathlib
import Definitions.Def_QueryDepthMIS_inducedDepth
import Definitions.Def_QueryDepthMIS_aliveSet
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- Lemma 2.13 (Query-depth division) (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 2.13, p.10): "For integers 1 ≤ l ≤ t < r ≤ n,
σ(G_alive(l, r)) ≤ σ(G_alive(l, t)) + σ(G_alive(t + 1, r)) + 1."

For every permutation and all integers `1 ≤ l ≤ t < r ≤ n`, the query depth of the alive graph
`G_alive(l, r)` is at most the sum of those of `G_alive(l, t)` and `G_alive(t + 1, r)` plus one;
each query depth is that of the induced subgraph with the inherited order (Definition 2.6).

**Formalization Note** Deterministic: it holds for every `ω`. `σ(G_alive(a, b))` is
`inducedDepth G (rank ω) (aliveSet G (rank ω) a b)`, the subgraph running its own greedy process
under the restricted ranks. -/
theorem lemma_2_13 :
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Perm V) (l t r : ℕ),
      1 ≤ l → l ≤ t → t < r → r ≤ Fintype.card V →
      inducedDepth G (rank ω) (aliveSet G (rank ω) l r) ≤
        inducedDepth G (rank ω) (aliveSet G (rank ω) l t) +
          inducedDepth G (rank ω) (aliveSet G (rank ω) (t + 1) r) + 1 := by sorry

end QueryDepthMIS
