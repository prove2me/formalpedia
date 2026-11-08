-- Prove2me | Theorems.Thm_TreeEdgeRankPC_tree_edge_ranking_in_p
-- name    : TreeEdgeRankPC.tree_edge_ranking_in_p
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:36.099909+00:00
-- url     : https://prove2.me/theorems/979e8a5d-c06f-4d90-a308-d7c14fd1eeec
-- title:
--   §4 — Tree-Edge-Ranking is in P (cited: de la Torre–Greenlaw–Schäffer; Lam–Yue)
-- statement:
--   Deciding, for a tree $T$ and an integer $K\ge0$, whether $\mathrm{er}(T)\le K$ is in P, and so is its restriction to trees of diameter at most six.
--
--   The paper cites this fact from the sequential algorithms of de la Torre, Greenlaw and Schäffer and of Lam and Yue; in this mission it is a theorem to prove, never a hypothesis.
--
--   Differences from the source:
--   - encoding: a polynomial-time algorithm on the instance (T, K) → a Cook one-tape machine on the code `encTree T K`, rejecting strings that encode no instance, `K` in binary; reason: the published `CookPvsNP.P Bool` is the class of p.12
--   - reading: "Tree-Edge-Ranking" → both the general and the diameter-six language; reason: Theorem 1.1 needs both, and the restriction check is polynomial
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §4, p.14 (Tree-Edge-Ranking in P, [dlTGS95, LY01])

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TreeEdgeRankPC_TreeLanguage

namespace TreeEdgeRankPC

/-- **Tree-Edge-Ranking is in P**, §4, p.14, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), citing [dlTGS95, LY01]: "Since Tree-Edge-Ranking is known to be in
P, it suffices to show P-hardness".

**Formalization Note.** The paper cites this fact. Here it is a theorem to prove, not a hypothesis of anything, for
both languages of Theorem 1.1. `K` is in binary and `T` an arbitrary tree; a machine for the languages must also
reject strings that encode no instance. -/
theorem tree_edge_ranking_in_p : TER ∈ CookPvsNP.P Bool ∧ TER6 ∈ CookPvsNP.P Bool := by sorry

end TreeEdgeRankPC
