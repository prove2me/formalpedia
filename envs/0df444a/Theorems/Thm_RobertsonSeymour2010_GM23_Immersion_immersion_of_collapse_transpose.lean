-- Prove2me | Theorems.Thm_RobertsonSeymour2010_GM23_Immersion_immersion_of_collapse_transpose
-- name    : RobertsonSeymour2010.GM23.Immersion.immersion_of_collapse_transpose
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:24.390184+00:00
-- url     : https://prove2.me/theorems/7aad6c11-a12d-4eba-9f81-2d1cb3074752
-- title:
--   1.3 — a collapse of the transpose of G to the transpose of H gives an immersion of H in G
-- statement:
--   Let $G,H$ be finite loopless graphs (parallel edges allowed), and let $G',H'$ be their transposes: $V(G')=E(G)$, $E(G')=V(G)$, with the incidence relation of $G$, and similarly for $H$. If
--   $$\text{there is a collapse of } G' \text{ to } H',$$
--   then there is an immersion of $H$ in $G$.
--
--   This lemma converts the hypergraph result 1.2 (applied to transposes) into the immersion theorem for loopless graphs.
--
--   **Formalization Note.** The transpose is `Graph.transpose`, a hypergraph whose vertex type is the edge type of the graph and vice versa. Looplessness of both graphs is a hypothesis, as in the paper.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 1.3, p. 2

import Mathlib
import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_Graphs

namespace RobertsonSeymour2010.GM23.Immersion

theorem immersion_of_collapse_transpose {VG EG VH EH : Type}
    [Fintype VG] [Fintype EG] [Fintype VH] [Fintype EH]
    (G : Graph VG EG) (H : Graph VH EH) (hG : G.Loopless) (hH : H.Loopless)
    (hη : Nonempty (Collapse G.transpose H.transpose)) :
    Nonempty (GraphImmersion H G) := by sorry

end RobertsonSeymour2010.GM23.Immersion
