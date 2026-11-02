-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_extension_maximal__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1
-- name    : WilliamsonShmoys.drawable_extension_maximal__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:54:01.867737+00:00
-- url     : https://prove2.me/theorems/b06c0b2b-14f6-429a-bbfd-d44f6c7645ab
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertex type. This removes the finite optimization step from the parent. Prove it by considering the finite set of simple graphs on V that contain P and are drawable, then choosing one with maximum edge count; any drawable strict extension would contradict maximality. The set is nonempty because it contains P. No vertex-count lower bound is needed for this step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_extension_maximal__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) [DecidableRel P.Adj] (hP : HasPlanarDrawingOn P) : ∃ Q : SimpleGraph V, ∃ hQdec : DecidableRel Q.Adj, P ≤ Q ∧ HasPlanarDrawingOn Q ∧ ∀ (R : SimpleGraph V) (hRdec : DecidableRel R.Adj), Q ≤ R → HasPlanarDrawingOn R → R ≤ Q := by sorry
