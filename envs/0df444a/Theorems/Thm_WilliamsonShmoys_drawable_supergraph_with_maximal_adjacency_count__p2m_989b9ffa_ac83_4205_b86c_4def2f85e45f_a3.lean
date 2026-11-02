-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_maximal_adjacency_count__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
-- name    : WilliamsonShmoys.drawable_supergraph_with_maximal_adjacency_count__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:18:02.486725+00:00
-- url     : https://prove2.me/theorems/7380dbd8-0282-416a-b2df-02034239de46
-- title:
--   Drawable supergraph maximizing adjacent-pair count
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type is contained in a drawable graph whose ordered adjacent-pair count is at least that of every drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_with_maximal_adjacency_count__p2m_989b9ffa_ac83_4205_b86c_4def2f85e45f_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H ∧
        ∀ K : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K →
            Nat.card {p : V × V // H.Adj p.1 p.2} ≥
              Nat.card {p : V × V // K.Adj p.1 p.2} := by sorry
