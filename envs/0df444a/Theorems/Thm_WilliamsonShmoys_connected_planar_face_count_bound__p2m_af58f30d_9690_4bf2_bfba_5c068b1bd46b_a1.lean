-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_count_bound__p2m_af58f30d_9690_4bf2_bfba_5c068b1bd46b_a1
-- name    : WilliamsonShmoys.connected_planar_face_count_bound__p2m_af58f30d_9690_4bf2_bfba_5c068b1bd46b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:53.590092+00:00
-- url     : https://prove2.me/theorems/2e66439f-db58-4f2d-a077-9b6daccbd657
-- title:
--   Euler face count and boundary bound for a connected drawable graph
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has a finite face count f satisfying Euler’s formula |V| + f = |E| + 2, while the sum of face boundary lengths gives 3f <= 2|E|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_face_count_bound__p2m_af58f30d_9690_4bf2_bfba_5c068b1bd46b_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hConnected : G.Connected) (hCard : 3 <= Fintype.card V) : Exists fun f : Nat => And (Fintype.card V + f = G.edgeSet.ncard + 2) (3 * f <= 2 * G.edgeSet.ncard) := by sorry
