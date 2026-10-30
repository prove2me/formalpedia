-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_of_maximal_planar_drawing__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1
-- name    : WilliamsonShmoys.connected_of_maximal_planar_drawing__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:49:28.447312+00:00
-- url     : https://prove2.me/theorems/64b9ded6-6a17-4826-8f9e-3b877457ad0a
-- title:
--   Maximal planar drawings are connected
-- statement:
--   An inclusion-maximal planar drawing on a finite vertex type is connected. The independent proof route is to assume two components exist and use the planar drawing to route an arc between vertices in distinct components, avoiding all other drawn edges and vertices. Adding that edge yields a planar strict supergraph, contradicting maximality. This isolates the topological edge-routing obligation from the parent’s finite maximality and assembly steps.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_of_maximal_planar_drawing__p2m_304864e8_bb51_44c5_aa36_393fdd5ea875_a1 {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (hmax : ∀ Z : SimpleGraph V, Y.edgeSet ⊂ Z.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn Z) : Y.Connected := by sorry
