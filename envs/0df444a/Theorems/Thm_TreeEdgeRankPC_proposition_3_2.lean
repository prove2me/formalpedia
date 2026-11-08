-- Prove2me | Theorems.Thm_TreeEdgeRankPC_proposition_3_2
-- name    : TreeEdgeRankPC.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:12.616757+00:00
-- url     : https://prove2.me/theorems/63c01536-6203-4014-9049-5b921e96cafa
-- title:
--   Proposition 3.2 — ranks at a vertex are valid iff admissible with pairwise disjoint $\kappa$ sets
-- statement:
--   Let $T$ be a tree rooted at $r$, let $v$ have children $v_1,\dots,v_d$, and fix valid edge rankings of the subtrees $T_{v_i}$ with visible sets $A_i$. Assigning ranks $c_1,\dots,c_d$ to the branches gives a valid edge ranking of $T_v$ if and only if
--
--   1. every $c_i$ is admissible for branch $i$, i.e. $c_i\notin A_i$, and
--   2. the sets $\kappa(A_i,c_i)$ are pairwise disjoint.
--
--   This local criterion is what reduces an edge ranking at a vertex to an allocation problem among its branches.
--
--   Differences from the source:
--   - encoding: a rooted tree T = (V, E) → `T : SimpleGraph V` with `T.IsTree`, `Fintype V`, and a root `r : V`; reason: Lean's graph type; the same objects
--   - encoding: the subtree T_v and branches as trees → graphs on the same vertex type with vertices outside isolated; reason: rankings, visibility and critical sets depend only on edges and walks from the root, so nothing changes
--   - encoding: fixed rankings of the T_{v_i} and ranks c_i → one function ρ, with c_i = ρ s(v, v_i); reason: these live on pairwise disjoint edge sets
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Proposition 3.2, p.11

import Mathlib
import Definitions.Def_TreeEdgeRankPC_EdgeRanking
import Definitions.Def_TreeEdgeRankPC_CriticalSet

namespace TreeEdgeRankPC

/-- **Proposition 3.2**, §3.1, p.11, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "Let v have children v1, ..., vd, and fix valid edge rankings of
the subtrees T_{vi} with visible sets Ai. Assigning ranks c1, ..., cd to the branches gives a valid edge
ranking of T_v if and only if every ci is admissible for branch i and the sets κ(Ai, ci) are pairwise
disjoint."

**Formalization Note.** The tree `T` is rooted at `r`, and `v` is an arbitrary vertex. The subtree rankings
live on pairwise disjoint edge sets and the branch ranks on the remaining edges of `T_v`, so one function
`ρ` carries them all: `c_i = ρ s(v, v_i)`. Ranks are positive on both sides of the equivalence: by
`IsEdgeRanking` on the left and by `ValidAssignment` on the right. -/
theorem proposition_3_2 {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree) (r v : V)
    (ρ : Sym2 V → ℕ) (hρ : ∀ c ∈ children T r v, IsEdgeRanking (subtree T r c) ρ) :
    IsEdgeRanking (subtree T r v) ρ ↔
      ValidAssignment (children T r v) (fun c => visible (subtree T r c) c ρ)
        (fun c => ρ s(v, c)) := by sorry

end TreeEdgeRankPC
