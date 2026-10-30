-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_planar_drawing__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
-- name    : WilliamsonShmoys.component_planar_drawing__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:21:37.285431+00:00
-- url     : https://prove2.me/theorems/ad903149-dee2-4bec-8ad3-d27d5001f908
-- title:
--   Restrict a planar drawing to a connected component
-- statement:
--   Restrict the vertex positions and edge arcs witnessing a planar drawing of a finite ordered graph to the subtype of vertices in one connected component. This applies without a component-size lower bound. Prove it by composing the witnesses with the subtype coercion and using the induced component graph adjacency, inherited order, and subtype injectivity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.component_planar_drawing__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    [Fintype C.supp] :
    WilliamsonShmoys.HasPlanarDrawingOn C.toSimpleGraph := by sorry
