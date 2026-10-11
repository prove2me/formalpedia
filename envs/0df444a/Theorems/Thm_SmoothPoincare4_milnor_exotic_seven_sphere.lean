-- Prove2me | Theorems.Thm_SmoothPoincare4_milnor_exotic_seven_sphere
-- name    : SmoothPoincare4.milnor_exotic_seven_sphere
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:50:39.964558+00:00
-- url     : https://prove2.me/theorems/c0719e91-4cce-4f77-aa94-840458ad96fb
-- title:
--   Milnor: an exotic 7-sphere exists
-- statement:
--   There is a smooth $7$-manifold $M$ that is homeomorphic to $S^7$ but not diffeomorphic to $S^7$.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Poincare conjecture' (posted by rybu, 2009), http://www.openproblemgarden.org/op/smooth_4_dimensional_poincare_conjecture

import Mathlib

open scoped Manifold ContDiff
open Metric

namespace SmoothPoincare4

theorem milnor_exotic_seven_sphere :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 7)) M)
      (_ : IsManifold (𝓡 7) ∞ M),
      Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) ∧
      IsEmpty (M ≃ₘ^∞⟮𝓡 7, 𝓡 7⟯ sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) := by sorry

end SmoothPoincare4
