-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension_f1f92bb7
-- name    : WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:54:50.091122+00:00
-- url     : https://prove2.me/theorems/89bdd873-d2df-48e0-8a91-c4a395c712f5
-- title:
--   Extending a finite planar drawing to a triangulation
-- statement:
--   A finite drawable simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly 3n−6 edges. At three vertices the extension is the triangle; otherwise it follows by extending to a triangulation and counting its faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
