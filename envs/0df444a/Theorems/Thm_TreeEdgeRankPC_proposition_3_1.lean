-- Prove2me | Theorems.Thm_TreeEdgeRankPC_proposition_3_1
-- name    : TreeEdgeRankPC.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:01.515824+00:00
-- url     : https://prove2.me/theorems/3d713c3d-5a68-4d5e-8501-18a44620607d
-- title:
--   Proposition 3.1 — $\mathrm{er}(T)=\max\mathrm{crit}(T)\le|T|-1$, regardless of the root
-- statement:
--   Let $T$ be a tree rooted at any vertex. Then
--   $$\mathrm{er}(T)=\max\mathrm{crit}(T)\le |T|-1,$$
--   where $|T|$ is the number of vertices, and the value does not depend on the chosen root.
--
--   This links the rooted notion of a critical set to the unrooted quantity the goal theorem is about.
--
--   Differences from the source:
--   - encoding: a rooted tree T = (V, E) → `T : SimpleGraph V` with `T.IsTree`, `Fintype V`, and a root `r : V`; reason: Lean's graph type; the same objects
--   - encoding: max crit(T) → `(crit T r).sup id`, which is 0 on the empty set; reason: er(T) = 0 for a one-vertex tree, p.15
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Proposition 3.1, p.10

import Mathlib
import Definitions.Def_TreeEdgeRankPC_EdgeRanking
import Definitions.Def_TreeEdgeRankPC_CriticalSet

namespace TreeEdgeRankPC

/-- **Proposition 3.1**, §3.1, p.10, Giliberti–Hajiaghayi–Yun, *Parallel Edge Ranking of Trees*,
arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "For a rooted tree T, er(T) = max crit(T) ≤ |T| − 1, regardless of the chosen root."

**Formalization Note.** `max` of the empty set is `0` via `Finset.sup id`, matching `er(T) = 0` for a
one-vertex tree (p.15). The root `r` is arbitrary. A tree has a vertex, so `Fintype.card V - 1` is exact. -/
theorem proposition_3_1 {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree) (r : V) :
    er T = (crit T r).sup id ∧ er T ≤ Fintype.card V - 1 := by sorry

end TreeEdgeRankPC
