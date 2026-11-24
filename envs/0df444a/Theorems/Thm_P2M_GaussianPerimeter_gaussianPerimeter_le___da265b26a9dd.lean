-- Prove2me | Theorems.Thm_P2M_GaussianPerimeter_gaussianPerimeter_le___da265b26a9dd
-- name    : P2M_GaussianPerimeter_gaussianPerimeter_le___da265b26a9dd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T10:09:48.860946+00:00
-- url     : https://prove2.me/theorems/0e87690f-3731-4863-89ce-3ef59ed2ec1b
-- title:
--   P2 M Gaussian Perimeter gaussian Perimeter le   da265b26a9dd: P2 M Gaussian Perimeter gaussian Perimeter le   da265b26a9dd
-- statement:
--   The maximal perimeter bounds the perimeter of each convex set.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Definitions.lean#L39-L41
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Definitions.lean#L39-L41

module
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Definitions.Def_GaussianPerimeter_Definitions
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal
open GaussianPerimeter

theorem P2M_GaussianPerimeter_gaussianPerimeter_le___da265b26a9dd {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : Convex ℝ K) : gaussianPerimeter K ≤ Γ n := by sorry

alias «GaussianPerimeter».«gaussianPerimeter_le_Γ» := P2M_GaussianPerimeter_gaussianPerimeter_le___da265b26a9dd
