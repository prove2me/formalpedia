-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_key
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:26.329813+00:00
-- url     : https://prove2.me/theorems/1037a341-4d0e-44cd-86b8-270bccbff93e
-- title:
--   Geometry Of Numbers Theory: sph Monom key
-- statement:
--   The Geometry Of Numbers Theory construction uses the sph Monom key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L97-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean#L97-L158

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
variable {N : ℕ}

theorem ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_key [NeZero N] {k : ℕ} (f : (Fin N → ℂ) → ℂ)
    (hf : ∀ (r : ℝ) (z : Fin N → ℂ), f (r • z) = (r : ℂ) ^ k * f z) :
    (∫ z, f z * (Real.exp (-sqN z) : ℂ)) *
        ((Real.Gamma ((((2 * N - 1 + 0 : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) =
      (∫ z, f ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ)) *
        ((Real.Gamma ((((2 * N - 1 + k : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) := by sorry
