-- Prove2me | Theorems.Thm_P2M_GaussianPerimeter_mul_lintegral_acceptance_le___90af1dc06317
-- name    : P2M_GaussianPerimeter_mul_lintegral_acceptance_le___90af1dc06317
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:13:11.772901+00:00
-- url     : https://prove2.me/theorems/c92c0aa3-aac5-4ff7-866c-6f11dfd7b1b3
-- title:
--   P2 M Gaussian Perimeter mul lintegral acceptance le   90af1dc06317: P2 M Gaussian Perimeter mul lintegral acceptance le   90af1dc06317
-- statement:
--   Average the lower bound from the strict facets of an intersection of
--   half-spaces with independent, uniformly distributed unit normals.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Averaging.lean#L53-L143
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Averaging.lean#L53-L143

module
public import Definitions.Def_GaussianPerimeter_Geometry
public import Definitions.Def_GaussianPerimeter_Sphere
public import Definitions.Def_GaussianPerimeter_Averaging
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace InnerProductSpace
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
local notation "UnitSphere" k => Metric.sphere (0 : Euc (k + 1)) 1

theorem P2M_GaussianPerimeter_mul_lintegral_acceptance_le___90af1dc06317 (k N : ℕ) (ρ : ℝ)
    (hvolume : (volume : Measure (Euc k)) ≤
      (volume (Metric.ball (0 : Euc k) 1) / (2 : ℝ≥0∞) ^ k) • μH[(k : ℝ)]) :
    ((N + 1 : ℕ) : ℝ≥0∞) *
      (∫⁻ y : Euc k, facetAcceptanceProbability k ρ ‖y‖ ^ N *
        ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
          Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))) ≤ Γ (k + 1) := by sorry

alias «GaussianPerimeter».«mul_lintegral_acceptance_le_Γ» := P2M_GaussianPerimeter_mul_lintegral_acceptance_le___90af1dc06317
