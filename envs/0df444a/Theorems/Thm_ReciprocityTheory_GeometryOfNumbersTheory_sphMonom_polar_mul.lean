-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_polar_mul
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_polar_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:30.918351+00:00
-- url     : https://prove2.me/theorems/6caa9261-936b-4b07-ae42-a0109da1b858
-- title:
--   Geometry Of Numbers Theory: sph Monom polar mul
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom polar mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L14-L33

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_polar_mul (μ : Measure E) [μ.IsAddHaarMeasure] (G : E → ℂ) (φ : ℝ → ℝ) :
    ∫ x, G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ =
      (∫ u : sphere (0 : E) 1, G u ∂μ.toSphere) *
        ((∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) : ℝ) : ℂ) := by sorry
