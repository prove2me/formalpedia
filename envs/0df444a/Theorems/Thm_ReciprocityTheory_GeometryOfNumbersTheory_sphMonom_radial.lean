-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_radial
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_radial
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:23.283935+00:00
-- url     : https://prove2.me/theorems/e36e5c0b-3800-5277-85c5-ef3533000ad1
-- title:
--   Geometry Of Numbers Theory: sph Monom radial
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L46-L61

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_radial (m k : ℕ) :
    ∫ r : Ioi (0 : ℝ), r.1 ^ k * Real.exp (-(r.1 ^ 2)) ∂(Measure.volumeIoiPow m) =
      Real.Gamma ((((m + k : ℕ) : ℝ) + 1) / 2) / 2 := by sorry
