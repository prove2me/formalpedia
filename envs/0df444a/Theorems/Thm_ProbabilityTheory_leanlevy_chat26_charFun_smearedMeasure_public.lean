-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat26_charFun_smearedMeasure_public
-- name    : ProbabilityTheory.leanlevy_chat26_charFun_smearedMeasure_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:38:16.610355+00:00
-- url     : https://prove2.me/theorems/11db2142-4299-4a6b-b7b5-4a85c7a2167e
-- title:
--   Public characteristic function formula for the smeared Levy measure
-- statement:
--   The smeared canonical Levy measure's characteristic function equals its Gaussian atom weight plus the Fourier transform of the sinc-deficit jump density.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LevyKhintchineUniqueness.lean lines 326-369, already Proved original private 3fd0ed06 via candidate31979.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat26_charFun_smearedMeasure_public
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (σ_sq : ℝ≥0) (ξ : ℝ) :
    charFun (smearedMeasure σ_sq ν) ξ
      = (((σ_sq : ℝ) / 6 : ℝ) : ℂ)
        + ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) ∂ν := by sorry
