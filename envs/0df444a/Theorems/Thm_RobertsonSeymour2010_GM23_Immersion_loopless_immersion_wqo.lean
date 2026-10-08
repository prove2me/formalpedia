-- Prove2me | Theorems.Thm_RobertsonSeymour2010_GM23_Immersion_loopless_immersion_wqo
-- name    : RobertsonSeymour2010.GM23.Immersion.loopless_immersion_wqo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:38.255441+00:00
-- url     : https://prove2.me/theorems/cfecf168-01d3-439f-ae2f-47a59b0635fb
-- title:
--   1.5 — vertex-labelled loopless graphs are well-quasi-ordered by immersion
-- statement:
--   Let $\Omega$ be a well-quasi-order, and for $i=1,2,\dots$ let $G_i$ be a finite loopless graph (parallel edges allowed) and $\phi_i:V(G_i)\to\Omega$ a labelling of its vertices. Then there exist $j>i\ge1$ and an immersion $\alpha$ of $G_i$ in $G_j$ such that
--   $$\phi_i(v)\le\phi_j(\alpha(v))\qquad\text{for all }v\in V(G_i).$$
--
--   Taking $\Omega=\mathbb N$ and labelling each vertex by its number of loops, 1.5 applied to the graphs with their loops deleted yields 1.1.
--
--   **Formalization Note.** The sequence is indexed from $0$; each $G_i$ lives on its own finite types. $\alpha(v)$ is the vertex component `α.vmap v` of the immersion.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 1.5, p. 3

import Mathlib
import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_Graphs

namespace RobertsonSeymour2010.GM23.Immersion

theorem loopless_immersion_wqo (Ω : Type) [Preorder Ω]
    (hΩ : WellQuasiOrdered (α := Ω) (· ≤ ·))
    (V E : ℕ → Type) [∀ i, Fintype (V i)] [∀ i, Fintype (E i)]
    (G : ∀ i, Graph (V i) (E i)) (hG : ∀ i, (G i).Loopless) (φ : ∀ i, V i → Ω) :
    ∃ i j : ℕ, i < j ∧ ∃ α : GraphImmersion (G i) (G j), ∀ v : V i, φ i v ≤ φ j (α.vmap v) := by sorry

end RobertsonSeymour2010.GM23.Immersion
