-- Prove2me | Theorems.Thm_Timetabling_StableHalf_stable_nset_iff_transversal
-- name    : Timetabling.StableHalf.stable_nset_iff_transversal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:41:23.369785+00:00
-- url     : https://prove2.me/theorems/b8e0e800-332d-4f74-a568-f918ddb8f9aa
-- title:
--   A stable set of $n$ nodes takes one node of each matched pair
-- statement:
--   Let $G$ be a graph on the $2n$ nodes $x_1, \bar x_1, \dots, x_n, \bar x_n$ in which $x_j$ and $\bar x_j$ are linked for every $j$. Then $G$ has a stable set of $n$ nodes if and only if it has a stable transversal: a choice of one node $(j, c_j)$ in every pair $\{x_j, \bar x_j\}$ such that the chosen nodes are pairwise non-adjacent.
--
--   In the proof of Proposition 2.4 this is why a stable set of $n$ nodes is a choice of one schedule per teacher, and why the backtracking can work with decisions $x_j$ or $\bar x_j$.
--
--   Differences from the source:
--   - generalization: the conflict graph G of a CT4 instance → any graph on Fin n × Bool with every (j, true) adjacent to (j, false); reason: the step uses only the matching edges; the conflict graph has them
--   - encoding: nodes x_j, x̄_j → Fin n × Bool, 0-based; reason: labelling only
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "(in particular, nodes x_j and x̄_j are linked)" and "a set of n pairwise non adjacent nodes (i.e. a stable set [1])". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_StableHalf_IsStableTransversal

namespace Timetabling.StableHalf

/-- **A stable set of `n` nodes takes one node of every matched pair.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"(in particular, nodes x_j and x̄_j are linked)" and "Then a timetable exists iff there is in G a
set of n pairwise non adjacent nodes (i.e. a stable set [1])."

Let `G` be a graph on `Fin n × Bool` in which `(j, true)` and `(j, false)` are adjacent for every
`j`. Then `G` has an independent set of `n` nodes if and only if it has a stable transversal: a
choice `c : Fin n → Bool` such that the nodes `(j, c j)` are pairwise non-adjacent. -/
theorem stable_nset_iff_transversal {n : ℕ} (G : SimpleGraph (Fin n × Bool))
    (hM : ∀ j, G.Adj (j, true) (j, false)) :
    (∃ s, G.IsNIndepSet n s) ↔ ∃ c : Fin n → Bool, IsStableTransversal G c := by sorry

end Timetabling.StableHalf
