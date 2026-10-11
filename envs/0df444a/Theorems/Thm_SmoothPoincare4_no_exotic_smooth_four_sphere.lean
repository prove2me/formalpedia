-- Prove2me | Theorems.Thm_SmoothPoincare4_no_exotic_smooth_four_sphere
-- name    : SmoothPoincare4.no_exotic_smooth_four_sphere
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:51:26.647983+00:00
-- url     : https://prove2.me/theorems/45330f85-54d5-4f3f-b005-bae142e1b74b
-- title:
--   No exotic smooth 4-sphere
-- statement:
--   Every smooth $4$-manifold that is homeomorphic to $S^4$ is diffeomorphic to $S^4$.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Poincare conjecture' (posted by rybu, 2009), http://www.openproblemgarden.org/op/smooth_4_dimensional_poincare_conjecture

import Mathlib

open scoped Manifold ContDiff
open Metric

namespace SmoothPoincare4

theorem no_exotic_smooth_four_sphere (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    (h : Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)) :
    Nonempty (M ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) := by sorry

end SmoothPoincare4
