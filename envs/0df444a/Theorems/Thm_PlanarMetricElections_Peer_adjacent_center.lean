-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_adjacent_center
-- name    : PlanarMetricElections.Peer.adjacent_center
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:47.334197+00:00
-- url     : https://prove2.me/theorems/906de69c-a328-4763-822d-a6d1b4cf585e
-- title:
--   Lemma A.7 — adjacent nonempty center cells
-- statement:
--   Let $V$ carry an exact quartile grid: its four rows and four columns each have mass $1/4$, cut lines contain no voters, and both coordinate projections are injective on $V$. Label its cells $A,B,C,D;E,F,G,H;I,J,K,L;M,N,O,P$, with rows from north to south, and use each cell letter for its uniform voter mass. Suppose
--
--   $$K=0,\quad F>0,\quad A\le G+J+F/2,\quad G>0,\quad J=0.$$
--
--   Then there is a selected voter set $Q$ such that
--
--   $$Q\subseteq V,\qquad |Q|\le3,\qquad\forall R\text{ axis-parallel rectangular},\quad\mu_V(R)>1/2\Longrightarrow Q\cap R\ne\varnothing.$$
--
--   This is the corresponding case lemma in the proof of the three-point strong rectangular half-net bound. The exact grid is a standing hypothesis of this case result only. The case with zero mass in $N\cup O$ remains included. The one-point rectangular $3/4$ upper bound cited within its proof is solver groundwork, not an added hypothesis.
--
--   Differences from the source:
--   - encoding: lettered cells in a north-to-south, west-to-east exact quartile grid → zero-based row/column indices in QuartileGrid; reason: the record spells out the standing grid, distinct-coordinate, and cut-avoidance assumptions; the sixteen cells are identical
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Lemma A.7, p. 18 (PDF p. 19)

import Definitions.Def_PlanarMetricElections_Peer_QuartileGrid

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer

theorem adjacent_center (V : Finset Plane) (g : QuartileGrid V)
    (hK : g.cellMass 2 2 = 0) (hF : 0 < g.cellMass 1 1)
    (hA : g.cellMass 0 0 ≤ g.cellMass 1 2 + g.cellMass 2 1 + g.cellMass 1 1 / 2)
    (hG : 0 < g.cellMass 1 2) (hJ : g.cellMass 2 1 = 0) :
    ∃ Q : Finset Plane, IsStrongRectNet V Q 3 (1 / 2) := by sorry

end PlanarMetricElections.Peer
