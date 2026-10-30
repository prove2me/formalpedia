-- Prove2me | Theorems.Thm_WilliamsonShmoys_connect_planar_components__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
-- name    : WilliamsonShmoys.connect_planar_components__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:45.457103+00:00
-- url     : https://prove2.me/theorems/70db2af0-0d6e-4990-9f4e-a19bbb8e6b51
-- title:
--   Join components in a planar drawing
-- statement:
--   This child handles disconnected drawings. The retained `hV` ensures the vertex type is nonempty, which is necessary for the existence of a connected graph on the same vertex set. The independent proof route is to use the finite planar drawing to add edges joining components one at a time, routing each new arc through the complement of the existing drawing without crossing its edges or passing through another vertex. Since the graph is extended, its edge count cannot decrease. This removes the component-joining construction from the parent; the remaining work in this child is to formalize the noncrossing arc construction for the given drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connect_planar_components__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, L.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
