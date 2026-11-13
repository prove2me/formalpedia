-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_one_center
-- name    : PlanarMetricElections.Peer.one_center
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:50.849002+00:00
-- url     : https://prove2.me/theorems/336d73ae-e695-4d36-b9a0-cf59886597a1
-- title:
--   Lemma A.9 — one nonempty center cell
-- statement:
--   Let $V$ carry an exact quartile grid with distinct coordinates and voter-free cuts, and label cells $A$ through $P$ in north-to-south row order. Write each cell letter for its voter mass. Under (14),
--
--   $$G=J=K=0,\qquad F>0,\qquad A\le F/2,$$
--
--   there is a strong rectangular half-net $Q$ with
--
--   $$Q\subseteq V,\quad |Q|\le3,\quad\forall R\text{ rectangular},\quad\mu_V(R)>1/2\Longrightarrow Q\cap R\ne\varnothing.$$
--
--   This includes all of the source's one-center configurations and supplies the last center-pattern case.
--
--   Differences from the source:
--   - encoding: lettered cells in a north-to-south, west-to-east exact quartile grid → zero-based row/column indices in QuartileGrid; reason: the record spells out the standing grid, distinct-coordinate, and cut-avoidance assumptions; the sixteen cells are identical
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Lemma A.9, p. 20 (PDF p. 21)

import Definitions.Def_PlanarMetricElections_Peer_QuartileGrid

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer

theorem one_center (V : Finset Plane) (g : QuartileGrid V)
    (hG : g.cellMass 1 2 = 0) (hJ : g.cellMass 2 1 = 0)
    (hK : g.cellMass 2 2 = 0) (hF : 0 < g.cellMass 1 1)
    (hA : g.cellMass 0 0 ≤ g.cellMass 1 1 / 2) :
    ∃ Q : Finset Plane, IsStrongRectNet V Q 3 (1 / 2) := by sorry

end PlanarMetricElections.Peer
