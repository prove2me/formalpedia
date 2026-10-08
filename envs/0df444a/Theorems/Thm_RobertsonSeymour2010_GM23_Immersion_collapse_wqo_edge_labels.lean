-- Prove2me | Theorems.Thm_RobertsonSeymour2010_GM23_Immersion_collapse_wqo_edge_labels
-- name    : RobertsonSeymour2010.GM23.Immersion.collapse_wqo_edge_labels
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:30.514997+00:00
-- url     : https://prove2.me/theorems/4da01e5a-61ef-4007-912d-f36ba46acf70
-- title:
--   1.4 — edge-labelled hypergraphs are well-quasi-ordered by collapse
-- statement:
--   Let $\Omega$ be a well-quasi-order, and for $i=1,2,\dots$ let $G_i$ be a finite hypergraph and $\phi_i:E(G_i)\to\Omega$ a labelling of its edges. Then there exist $j>i\ge1$ and a collapse $\eta$ of $G_j$ to $G_i$ such that
--   $$\phi_i(e)\le\phi_j(\eta(e))\qquad\text{for all }e\in E(G_i).$$
--
--   This strengthens 1.2 by labels; the paper needs it to handle loops when deducing 1.1.
--
--   **Formalization Note.** $\Omega$ is a type with a preorder that is `WellQuasiOrdered` (every sequence has $i<j$ with $x_i\le x_j$). The sequence is indexed from $0$. The hypergraphs $G_i$ live on their own finite types.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 1.4, p. 3

import Mathlib
import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_Graphs

namespace RobertsonSeymour2010.GM23.Immersion

theorem collapse_wqo_edge_labels (Ω : Type) [Preorder Ω]
    (hΩ : WellQuasiOrdered (α := Ω) (· ≤ ·))
    (V E : ℕ → Type) [∀ i, Fintype (V i)] [∀ i, Fintype (E i)]
    (G : ∀ i, Hypergraph (V i) (E i)) (φ : ∀ i, E i → Ω) :
    ∃ i j : ℕ, i < j ∧ ∃ η : Collapse (G j) (G i), ∀ e : E i, φ i e ≤ φ j (η.emap e) := by sorry

end RobertsonSeymour2010.GM23.Immersion
