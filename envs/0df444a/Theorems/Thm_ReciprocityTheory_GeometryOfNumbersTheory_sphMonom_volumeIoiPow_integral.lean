-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_volumeIoiPow_integral
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_volumeIoiPow_integral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:11.030191+00:00
-- url     : https://prove2.me/theorems/7e4c667f-79d5-4244-ba7d-07a1da068e18
-- title:
--   Geometry Of Numbers Theory: sph Monom volume Ioi Pow integral
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom volume Ioi Pow integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L37-L44

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_volumeIoiPow_integral (m : ℕ) (φ : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow m) = ∫ r in Ioi (0 : ℝ), r ^ m * φ r := by sorry
