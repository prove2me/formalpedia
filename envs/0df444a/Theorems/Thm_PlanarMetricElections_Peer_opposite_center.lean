-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_opposite_center
-- name    : PlanarMetricElections.Peer.opposite_center
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:38.502272+00:00
-- url     : https://prove2.me/theorems/d111bacb-7a34-4fe4-9579-4a03e14f9c37
-- title:
--   Lemma A.4 — opposite nonempty center cells
-- statement:
--   Let $V$ carry an exact quartile grid: its four rows and four columns each have mass $1/4$, cut lines contain no voters, and both coordinate projections are injective on $V$. Label its cells $A,B,C,D;E,F,G,H;I,J,K,L;M,N,O,P$, with rows from north to south, and use each cell letter for its uniform voter mass. Suppose
--
--   $$(F>0,\ K>0,\ G=J=0)\quad\text{or}\quad(G>0,\ J>0,\ F=K=0).$$
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
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Lemma A.4, p. 15 (PDF p. 16)

import Definitions.Def_PlanarMetricElections_Peer_QuartileGrid

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer

theorem opposite_center (V : Finset Plane) (g : QuartileGrid V)
    (hopposite :
      (0 < g.cellMass 1 1 ∧ 0 < g.cellMass 2 2 ∧
        g.cellMass 1 2 = 0 ∧ g.cellMass 2 1 = 0) ∨
      (0 < g.cellMass 1 2 ∧ 0 < g.cellMass 2 1 ∧
        g.cellMass 1 1 = 0 ∧ g.cellMass 2 2 = 0)) :
    ∃ Q : Finset Plane, IsStrongRectNet V Q 3 (1 / 2) := by sorry

end PlanarMetricElections.Peer
