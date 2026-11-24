-- Prove2me | Theorems.Thm_P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6
-- name    : P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:08:42.89128+00:00
-- url     : https://prove2.me/theorems/85e7cb7b-331b-4acd-b430-79d11cc05d38
-- title:
--   P2 M Gaussian Perimeter Volume Comparison append measurable  f5f150faf8d6: P2 M Gaussian Perimeter Volume Comparison append measurable  f5f150faf8d6
-- statement:
--   The P2 M Gaussian Perimeter Volume Comparison append measurable  f5f150faf8d6 construction uses the P2 M Gaussian Perimeter Volume Comparison append measurable  f5f150faf8d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L534-L538
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/PrekopaLeindler.lean#L534-L538

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise

theorem P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6 {d : ℕ} (t : Fin 1 → ℝ) : Measurable (fun x : Fin d → ℝ ↦ append x t) := by sorry

alias «GaussianPerimeter».«VolumeComparison».«append_measurable'» := P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6
