-- Prove2me | Theorems.Thm_TreeEdgeRankPC_proposition_4_4
-- name    : TreeEdgeRankPC.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:38.261756+00:00
-- url     : https://prove2.me/theorems/8b7fcd39-f40a-41a9-aa9d-58de3e019b71
-- title:
--   Proposition 4.4 — $X$ is realizable for a branch iff $\mathrm{wt}(X)\ge\mathrm{wt}(\mathrm{crit}(B))$
-- statement:
--   Let a tree $T$ have root $v$ and branches $B_1,\dots,B_d$, each including its edge incident to $v$ and rooted at $v$, and let $X$ be a set of ranks. Then $X$ is realizable for a branch $B$ if and only if
--   $$\mathrm{wt}(X)\ge\mathrm{wt}(\mathrm{crit}(B)).$$
--   Consequently, $X$ is realizable for $T$ if and only if it contains pairwise disjoint subsets $X_1,\dots,X_d$ with $\mathrm{wt}(X_i)\ge\mathrm{wt}(\mathrm{crit}(B_i))$ for each $i$.
--
--   This is what makes a branch act as a single numerical requirement, and so links edge rankings to GreedyAllocation.
--
--   Differences from the source:
--   - encoding: a rooted tree T = (V, E) → `T : SimpleGraph V` with `T.IsTree`, `Fintype V`, and a root `r : V`; reason: Lean's graph type; the same objects
--   - encoding: the subtree T_v and branches as trees → graphs on the same vertex type with vertices outside isolated; reason: rankings, visibility and critical sets depend only on edges and walks from the root, so nothing changes
--   - encoding: a set of ranks X → a finite set of positive integers; reason: ranks are positive by definition; rank 0 would have `wt` 1 under natural-number subtraction
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Proposition 4.4, p.15

import Mathlib
import Definitions.Def_TreeEdgeRankPC_EdgeRanking
import Definitions.Def_TreeEdgeRankPC_CriticalSet

namespace TreeEdgeRankPC

/-- **Proposition 4.4**, §4.1, p.15, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "A set of ranks X is realizable for a branch B if and only if
wt(X) ≥ wt(crit(B)). Consequently, X is realizable for T if and only if it contains pairwise disjoint subsets
X1, ..., Xd with wt(Xi) ≥ wt(crit(Bi)) for each i = 1, ..., d."

**Formalization Note.** The tree `T` has root `v`, whose children are its neighbours, and `B_i = branch T v c`
for a child `c`, rooted at `v` (p.15). Every branch `B` arises this way, from `T = B`. `X` is any finite set of
positive ranks, not necessarily `[K]`. -/
theorem proposition_4_4 {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree) (v : V)
    (X : Finset ℕ) (hX : IsRankSet X) :
    (∀ c ∈ children T v v,
      (Realizable (branch T v c) v X ↔ wt (crit (branch T v c) v) ≤ wt X)) ∧
    (Realizable T v X ↔ ∃ Xs : V → Finset ℕ,
      (∀ c ∈ children T v v, Xs c ⊆ X ∧ wt (crit (branch T v c) v) ≤ wt (Xs c)) ∧
      (↑(children T v v) : Set V).PairwiseDisjoint Xs) := by sorry

end TreeEdgeRankPC
