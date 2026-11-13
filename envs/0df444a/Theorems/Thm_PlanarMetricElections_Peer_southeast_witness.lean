-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_southeast_witness
-- name    : PlanarMetricElections.Peer.southeast_witness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:44.523857+00:00
-- url     : https://prove2.me/theorems/b7d528b1-8e9b-4ba7-befc-4f585963b782
-- title:
--   Lemma A.8 — southeast witness criterion
-- statement:
--   Let $V$ carry the exact quartile grid with distinct coordinates and voter-free cuts. Cells are labeled $A$ through $P$ in row order north to south and column order west to east, and cell letters denote their masses. Assume the standing conditions (14):
--
--   $$G=J=K=0,\qquad F>0,\qquad A\le F/2.$$
--
--   Let $p$ be the middle-cut intersection, and put $\tau=\max\{A,1/4-F\}$. Let $q_3\in V$ satisfy $q_{3,1}>p_1$ and $q_{3,2}<p_2$. Suppose $Z_E,Z_S\subseteq V$ each avoid the first row, first column, and cell $F$, and satisfy
--
--   $$Z_E\subseteq\{z:z_1\ge q_{3,1}\},\quad Z_S\subseteq\{z:z_2\le q_{3,2}\},\quad\mu_V(Z_E)\ge\tau,\quad\mu_V(Z_S)\ge\tau.$$
--
--   Then the specific selected set
--
--   $$Q=\{\operatorname{East}(F\cap V),\operatorname{South}(F\cap V),q_3\}$$
--
--   is a strong rectangular $1/2$-net for $V$ and has size at most three. The easternmost and southernmost points can coincide. The witness sets can overlap and need not be rectangles. This criterion is used by the one-nonempty-center case.
--
--   Differences from the source:
--   - encoding: lettered cells in a north-to-south, west-to-east exact quartile grid → zero-based row/column indices in QuartileGrid; reason: the record spells out the standing grid, distinct-coordinate, and cut-avoidance assumptions; the sixteen cells are identical
--   - encoding: sets ZE and ZS contained in the finite electorate → finite subsets ZE and ZS; reason: every subset of a finite set has a unique finite-set representation; no extra restriction is imposed
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Lemma A.8, p. 20 (PDF p. 21)

import Definitions.Def_PlanarMetricElections_Peer_QuartileGrid
import Definitions.Def_PlanarMetricElections_Peer_ExtremePoints

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer

theorem southeast_witness (V : Finset Plane) (g : QuartileGrid V)
    (hG : g.cellMass 1 2 = 0) (hJ : g.cellMass 2 1 = 0)
    (hK : g.cellMass 2 2 = 0) (hF : 0 < g.cellMass 1 1)
    (hA : g.cellMass 0 0 ≤ g.cellMass 1 1 / 2)
    (q3 : Plane) (hq : q3 ∈ V)
    (hEast : g.middle.1 < q3.1) (hSouth : q3.2 < g.middle.2)
    (ZE ZS : Finset Plane) (hZE : ZE ⊆ V) (hZS : ZS ⊆ V)
    (hZErow : Disjoint (↑ZE : Set Plane) (rowBand g.yCut 0))
    (hZEcol : Disjoint (↑ZE : Set Plane) (columnBand g.xCut 0))
    (hZEF : Disjoint (↑ZE : Set Plane) (g.cell 1 1))
    (hZSrow : Disjoint (↑ZS : Set Plane) (rowBand g.yCut 0))
    (hZScol : Disjoint (↑ZS : Set Plane) (columnBand g.xCut 0))
    (hZSF : Disjoint (↑ZS : Set Plane) (g.cell 1 1))
    (hZEEast : ∀ z ∈ ZE, q3.1 ≤ z.1) (hZSSouth : ∀ z ∈ ZS, z.2 ≤ q3.2)
    (hZEmass : g.tau ≤ mass V (↑ZE : Set Plane))
    (hZSmass : g.tau ≤ mass V (↑ZS : Set Plane)) :
    IsStrongRectNet V {eastPoint (g.cellVotes 1 1), southPoint (g.cellVotes 1 1), q3}
      3 (1 / 2) := by sorry

end PlanarMetricElections.Peer
