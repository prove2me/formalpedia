-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_fintype
-- name    : WilliamsonShmoys.connected_component_fintype
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:34:59.961307+00:00
-- url     : https://prove2.me/theorems/81e86b09-ea25-42af-94db-478b7dfb533b
-- title:
--   Finiteness of connected components
-- statement:
--   A finite graph has a finite type of connected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.connected_component_fintype
    {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    Nonempty (Fintype G.ConnectedComponent) := by sorry
