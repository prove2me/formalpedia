-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_instance_irrel__p2m_160c891e_c18d_4863_b495_0a238ee51219_a3
-- name    : WilliamsonShmoys.edgeFinset_card_instance_irrel__p2m_160c891e_c18d_4863_b495_0a238ee51219_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:18:18.79708+00:00
-- url     : https://prove2.me/theorems/9e61d566-1c91-4243-81fe-c174cc105ed1
-- title:
--   Edge finset cardinality is independent of the finite instance
-- statement:
--   For a finite graph, the number of edges in its edge finset is the same whether the edge-set subtype uses the default finite instance or the graph’s canonical finite instance.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.edgeFinset_card_instance_irrel__p2m_160c891e_c18d_4863_b495_0a238ee51219_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
     G.edgeFinset.card) =
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : Fintype ↑G.edgeSet := G.fintypeEdgeSet
     G.edgeFinset.card) := by sorry
