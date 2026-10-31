-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_connected_supergraph__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
-- name    : WilliamsonShmoys.drawable_connected_supergraph__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:17:53.172558+00:00
-- url     : https://prove2.me/theorems/758bf2e9-7bcb-4b8d-aa3d-e60bbb182390
-- title:
--   Planar drawing extends to a connected supergraph
-- statement:
--   A finite graph with the supplied planar drawing has a connected planar supergraph on the same vertex set. The parent uses the supergraph to apply the connected edge bound, then transfers the result using monotonicity of edgeFinset.card. The vertex-count hypothesis is retained for the connected bound and covers isolated vertices in the construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_connected_supergraph__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V,
      M ≤ G ∧ G.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
