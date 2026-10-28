-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_maximal_extension_c00979a8
-- name    : WilliamsonShmoys.connected_planar_maximal_extension_c00979a8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:42:16.92076+00:00
-- url     : https://prove2.me/theorems/d6f36996-8531-4740-91bd-ffaf29e500e4
-- title:
--   Maximal planar extension on the same vertices
-- statement:
--   Extend the connected drawn graph to an inclusion-maximal drawn supergraph on the same vertices, retaining connectedness and at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_maximal_extension_c00979a8 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ L.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ (∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) ∧ K.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
