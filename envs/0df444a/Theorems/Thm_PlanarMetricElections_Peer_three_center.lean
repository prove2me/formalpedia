-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_three_center
-- name    : PlanarMetricElections.Peer.three_center
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:38.449471+00:00
-- url     : https://prove2.me/theorems/5ca84720-9611-4368-9e36-e90e812b25ad
-- title:
--   Lemma A.6 — three nonempty center cells
-- statement:
--   Let $V$ carry an exact quartile grid: its four rows and four columns each have mass $1/4$, cut lines contain no voters, and both coordinate projections are injective on $V$. Label its cells $A,B,C,D;E,F,G,H;I,J,K,L;M,N,O,P$, with rows from north to south, and use each cell letter for its uniform voter mass. Suppose
--
--   $$K=0,\quad F>0,\quad A\le G+J+F/2,\quad G>0,\quad J>0.$$
--
--   Then there is a selected voter set $Q$ such that
--
--   $$Q\subseteq V,\qquad |Q|\le3,\qquad\forall R\text{ axis-parallel rectangular},\quad\mu_V(R)>1/2\Longrightarrow Q\cap R\ne\varnothing.$$
--
--   This is the corresponding case lemma in the proof of the three-point strong rectangular half-net bound. The exact grid is a standing hypothesis of this case result only.
--
--   Differences from the source:
--   - encoding: lettered cells in a north-to-south, west-to-east exact quartile grid → zero-based row/column indices in QuartileGrid; reason: the record spells out the standing grid, distinct-coordinate, and cut-avoidance assumptions; the sixteen cells are identical
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Lemma A.6, p. 17 (PDF p. 18)

import Definitions.Def_PlanarMetricElections_Peer_QuartileGrid

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer

theorem three_center (V : Finset Plane) (g : QuartileGrid V)
    (hK : g.cellMass 2 2 = 0) (hF : 0 < g.cellMass 1 1)
    (hA : g.cellMass 0 0 ≤ g.cellMass 1 2 + g.cellMass 2 1 + g.cellMass 1 1 / 2)
    (hG : 0 < g.cellMass 1 2) (hJ : 0 < g.cellMass 2 1) :
    ∃ Q : Finset Plane, IsStrongRectNet V Q 3 (1 / 2) := by sorry

end PlanarMetricElections.Peer
