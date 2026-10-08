-- Prove2me | Theorems.Thm_Timetabling85_CourseColoring_prop_3_2
-- name    : Timetabling85.CourseColoring.prop_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:09.264446+00:00
-- url     : https://prove2.me/theorems/b240bbd1-3755-48c1-8257-08a8570939f4
-- title:
--   Proposition 3.2, p. 158 — removing consistently precolored lecture-nodes gives Ĝ′: Ĝ has a p-coloring respecting the precoloring iff Ĝ′ is p-colorable
-- statement:
--   Let $H$ be a course scheduling graph: its nodes are lecture-nodes $V$ and period-nodes $1,\dots,p$, and all pairs of period-nodes are adjacent. Assume some lecture-nodes have been precoloured: a precoloured node $v$ must receive the colour of the period-node $k(v)$. Assume the precolouring is **consistent**:
--
--   1. no precoloured node $v$ is adjacent to its own period-node $k(v)$, and
--   2. no two adjacent lecture-nodes are precoloured with the colour of the same period-node.
--
--   Let $\hat G'$ be obtained from $H$ by removing every precoloured node $v$ and linking each of its remaining neighbours with the period-node $k(v)$; $\hat G'$ has no precoloured node. Then
--   $$H \text{ has a node coloring with } p \text{ colors respecting the precoloring} \iff \hat G' \text{ has a node coloring with } p \text{ colors}.$$
--
--   For node colouring, unlike edge colouring, preassignments therefore do not make the problem harder: they can be absorbed into the graph.
--
--   **Formalization Note** The consistency hypotheses are an addition to the page, and a necessary one: if two adjacent lecture-nodes are precoloured with the same colour, $H$ has no respecting colouring, but removing both deletes the edge between them and $\hat G'$ may be $p$-colourable (two adjacent lecture-nodes and one period-node, $p = 1$). The proof on the page also speaks of a 1–1 correspondence between the colourings; with precolours read as fixed absolute colours this fails (colourings of $\hat G'$ may permute the colours of the period-nodes), so only the equivalence of the proposition is stated. "Precoloured" is read relative to the period-nodes ($c(v) = c(k(v))$), as in the proof of Proposition 3.1; since the period-nodes form a clique on $p$ nodes, this is equivalent to precolouring with absolute colours up to a permutation of the palette. $H$ is any graph with this shape; the graph $\hat G$ of Proposition 3.1 is one.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), p. 158, Proposition 3.2 and its proof

import Mathlib
import Definitions.Def_Timetabling85_CourseColoring_CSUP

namespace Timetabling85.CourseColoring

theorem prop_3_2 {V : Type*} {p : ℕ} (H : SimpleGraph (V ⊕ Fin p)) (pc : V → Option (Fin p))
    (hclique : ∀ k k' : Fin p, k ≠ k' → H.Adj (Sum.inr k) (Sum.inr k'))
    (hcons_period : ∀ (v : V) (k : Fin p), pc v = some k → ¬ H.Adj (Sum.inl v) (Sum.inr k))
    (hcons_lecture : ∀ (v v' : V) (k : Fin p), pc v = some k → pc v' = some k →
      ¬ H.Adj (Sum.inl v) (Sum.inl v')) :
    (∃ c : H.Coloring (Fin p), ∀ (v : V) (k : Fin p), pc v = some k →
        c (Sum.inl v) = c (Sum.inr k)) ↔
      (removePrecolored H pc).Colorable p := by sorry

end Timetabling85.CourseColoring
