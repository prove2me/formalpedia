-- Prove2me | Theorems.Thm_SmoothPoincare4_continuum_exotic_R4
-- name    : SmoothPoincare4.continuum_exotic_R4
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:51:04.514871+00:00
-- url     : https://prove2.me/theorems/7e87b1bf-8da8-46d6-99ae-b309565716db
-- title:
--   A continuum of exotic smooth structures on ℝ⁴
-- statement:
--   There is a family $(X_t)_{t \in \mathbb{R}}$ of smooth $4$-manifolds, each homeomorphic to $\mathbb{R}^4$, such that $X_s$ and $X_t$ are not diffeomorphic whenever $s \ne t$.
-- source:
--   Open Problem Garden, 'Smooth 4-dimensional Poincare conjecture' (posted by rybu, 2009), http://www.openproblemgarden.org/op/smooth_4_dimensional_poincare_conjecture

import Mathlib

open scoped Manifold ContDiff
open Metric

namespace SmoothPoincare4

theorem continuum_exotic_R4 :
    ∃ (X : ℝ → Type) (_ : ∀ t, TopologicalSpace (X t))
      (_ : ∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 4)) (X t))
      (_ : ∀ t, IsManifold (𝓡 4) ∞ (X t)),
      (∀ t, Nonempty (X t ≃ₜ EuclideanSpace ℝ (Fin 4))) ∧
      ∀ s t, s ≠ t → IsEmpty (X s ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ X t) := by sorry

end SmoothPoincare4
