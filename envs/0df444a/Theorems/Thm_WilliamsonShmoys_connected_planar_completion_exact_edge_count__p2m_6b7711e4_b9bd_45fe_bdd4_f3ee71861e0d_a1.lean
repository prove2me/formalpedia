-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_completion_exact_edge_count__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
-- name    : WilliamsonShmoys.connected_planar_completion_exact_edge_count__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:05.356822+00:00
-- url     : https://prove2.me/theorems/bd02a62a-20ac-45ba-a540-81b91c2ce75e
-- title:
--   Connected planar graphs have an exact-count completion
-- statement:
--   This supplies the main reusable topological result used by the parent: a connected drawable simple graph with at least three vertices can be extended on the same vertex type to a drawable graph with exactly 3|V|−6 edges. A proof route is to add drawable edges until the finite set of possible edges is exhausted, show that an inclusion-maximal plane simple graph has triangular faces, and combine 3F=2E with Euler’s formula. The triangle case is included by the stated cardinality bound. This is the main remaining mathematical obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_completion_exact_edge_count__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) (hConn : K.Connected) : ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ 3 * Fintype.card V - 6 = H.edgeSet.ncard := by sorry
