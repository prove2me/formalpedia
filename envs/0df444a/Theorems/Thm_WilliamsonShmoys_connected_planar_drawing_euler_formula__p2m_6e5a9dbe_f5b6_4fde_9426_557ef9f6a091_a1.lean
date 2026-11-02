-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_formula__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_formula__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:22:13.672803+00:00
-- url     : https://prove2.me/theorems/46b6680b-c62d-4b45-898f-f92e675885e6
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   Every finite connected graph with at least three vertices and a crossing-free drawing has a natural face count satisfying Euler’s formula |V| + f = |E| + 2. Prove by obtaining the finite plane embedding from the drawing and applying the Euler formula for connected plane graphs; the vertex-count lower bound is retained to match the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_formula__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    ∃ f : Nat, Fintype.card V + f = K.edgeFinset.card + 2 := by sorry
