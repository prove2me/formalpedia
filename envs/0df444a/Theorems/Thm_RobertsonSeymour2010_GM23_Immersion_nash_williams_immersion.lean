-- Prove2me | Theorems.Thm_RobertsonSeymour2010_GM23_Immersion_nash_williams_immersion
-- name    : RobertsonSeymour2010.GM23.Immersion.nash_williams_immersion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:37.531582+00:00
-- url     : https://prove2.me/theorems/e44dcfe7-5702-49fa-9248-9a464cc8d2bf
-- title:
--   1.1 — Nash-Williams' immersion conjecture: in every infinite sequence of finite graphs, some graph is immersed in a later one
-- statement:
--   For every sequence $G_1,G_2,\dots$ of finite graphs, in which loops and parallel edges are allowed, there exist
--   $$j>i\ge1\quad\text{such that there is an immersion of }G_i\text{ in }G_j .$$
--
--   Equivalently, finite graphs are well-quasi-ordered by the immersion relation. This was conjectured by Nash-Williams and is one of the two main results of the paper.
--
--   **Formalization Note.** The sequence is a family of graphs `G i : Graph (V i) (E i)` on their own finite types, indexed from $0$, so the paper's $j>i\ge1$ becomes $i<j$ in $\mathbb N$. An immersion is the structure `GraphImmersion (G i) (G j)`: an injective vertex map, a path of $G_j$ for each non-loop edge (between the images of its ends), a circuit through the image vertex for each loop, and pairwise edge-disjointness of these paths and circuits.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 1.1, p. 1

import Mathlib
import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_Graphs

namespace RobertsonSeymour2010.GM23.Immersion

theorem nash_williams_immersion (V E : ℕ → Type) [∀ i, Fintype (V i)] [∀ i, Fintype (E i)]
    (G : ∀ i, Graph (V i) (E i)) :
    ∃ i j : ℕ, i < j ∧ Nonempty (GraphImmersion (G i) (G j)) := by sorry

end RobertsonSeymour2010.GM23.Immersion
