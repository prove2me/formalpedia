-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_maximal_extension_037368dd_04cc_4345_b537_96bdbb1ae146
-- name    : WilliamsonShmoys.drawable_maximal_extension_037368dd_04cc_4345_b537_96bdbb1ae146
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:01:17.494763+00:00
-- url     : https://prove2.me/theorems/11cc7605-1289-4618-b500-3a593df9b767
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs, with at least as many edges. Finiteness of the set of simple graphs on V gives a maximum-edge choice; a proper supergraph would strictly increase its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_maximal_extension_037368dd_04cc_4345_b537_96bdbb1ae146
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ H : SimpleGraph V,
      X ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      X.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
