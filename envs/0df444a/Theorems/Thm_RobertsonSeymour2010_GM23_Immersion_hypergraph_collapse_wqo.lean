-- Prove2me | Theorems.Thm_RobertsonSeymour2010_GM23_Immersion_hypergraph_collapse_wqo
-- name    : RobertsonSeymour2010.GM23.Immersion.hypergraph_collapse_wqo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:32.233686+00:00
-- url     : https://prove2.me/theorems/779e71bf-63d8-4507-9bb8-45a282975d52
-- title:
--   1.2 — finite hypergraphs are well-quasi-ordered by collapse
-- statement:
--   For every sequence $G_1,G_2,\dots$ of finite hypergraphs there exist
--   $$j>i\ge1\quad\text{such that there is a collapse of }G_j\text{ to }G_i .$$
--
--   When all $G_i$ are loopless graphs, a collapse of $G_j$ to $G_i$ makes $G_i$ isomorphic to a minor of $G_j$, so 1.2 contains Wagner's conjecture for loopless graphs. Together with 1.3 applied to transposes it gives 1.1 for loopless graphs.
--
--   **Formalization Note.** The sequence is a family of hypergraphs on their own finite types `V i`, `E i`, indexed from $0$. A collapse of $G_j$ to $G_i$ maps $G_i$ into $G_j$.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 1.2, p. 2

import Mathlib
import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_Graphs

namespace RobertsonSeymour2010.GM23.Immersion

theorem hypergraph_collapse_wqo (V E : ℕ → Type) [∀ i, Fintype (V i)] [∀ i, Fintype (E i)]
    (G : ∀ i, Hypergraph (V i) (E i)) :
    ∃ i j : ℕ, i < j ∧ Nonempty (Collapse (G j) (G i)) := by sorry

end RobertsonSeymour2010.GM23.Immersion
