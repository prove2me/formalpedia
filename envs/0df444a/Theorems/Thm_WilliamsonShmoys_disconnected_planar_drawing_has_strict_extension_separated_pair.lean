-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_strict_extension_separated_pair
-- name    : WilliamsonShmoys.disconnected_planar_drawing_has_strict_extension_separated_pair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:34:39.442987+00:00
-- url     : https://prove2.me/theorems/2941f424-7cd7-43c2-b02d-9a7a91370556
-- title:
--   Disconnectedness yields separated vertices
-- statement:
--   A finite graph on at least three vertices that is not connected has two distinct vertices in different reachability components. This supplies the endpoints needed by the geometric augmentation lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_planar_drawing_has_strict_extension_separated_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v := by sorry
