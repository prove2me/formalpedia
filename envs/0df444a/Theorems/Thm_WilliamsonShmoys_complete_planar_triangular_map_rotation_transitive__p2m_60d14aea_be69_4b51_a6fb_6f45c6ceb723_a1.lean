-- Prove2me | Theorems.Thm_WilliamsonShmoys_complete_planar_triangular_map_rotation_transitive__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
-- name    : WilliamsonShmoys.complete_planar_triangular_map_rotation_transitive__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:04:18.207108+00:00
-- url     : https://prove2.me/theorems/b6f5758e-dc62-475d-9052-43aa820ea959
-- title:
--   A complete planar triangular map has transitive local rotation
-- statement:
--   For a complete planar graph with the stated triangular dart data, any two darts with the same tail are connected by iterating the induced local successor.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.complete_planar_triangular_map_rotation_transitive__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f))
    (hCovered : ∀ v, ∃ f i, corner f i = v)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v) :
    ∀ d e : H.Dart, d.fst = e.fst →
      ∃ k : Nat,
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e := by sorry
