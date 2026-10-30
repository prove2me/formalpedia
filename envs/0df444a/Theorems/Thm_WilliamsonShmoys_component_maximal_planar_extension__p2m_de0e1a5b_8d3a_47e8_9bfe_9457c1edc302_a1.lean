-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_maximal_planar_extension__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
-- name    : WilliamsonShmoys.component_maximal_planar_extension__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:02:38.327993+00:00
-- url     : https://prove2.me/theorems/16ddb684-8eab-45f4-881b-4391d956c1ce
-- title:
--   Extend a drawable component to a maximal planar supergraph
-- statement:
--   Restrict the given drawing to the subtype of vertices in the component, then choose a drawable supergraph maximal under adding edges on that same finite vertex set. The finite instance on the subtype is explicit because the previous child failed to synthesize it. This removes drawing restriction and finite maximal-extension construction from the parent. An independent route is to restrict the drawing witnesses, form the finite collection of drawable supergraphs containing the component graph, and choose a maximal member. No lower bound on component size is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.component_maximal_planar_extension__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    [Fintype C.supp] :
    ∃ M : SimpleGraph C.supp,
      C.toSimpleGraph.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph C.supp, M ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M) := by sorry
