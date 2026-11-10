-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat26b_intInt_exponent_jump
-- name    : ProbabilityTheory.leanlevy_chat26b_intInt_exponent_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:33:16.60144+00:00
-- url     : https://prove2.me/theorems/5e62d8da-8df9-4915-9ba9-0d7e0461d668
-- title:
--   Fubini identity for the compensated Levy jump exponent smear
-- statement:
--   Fubini's theorem exchanges the bounded symmetric frequency interval with integration under a Levy measure, and the source pointwise compensated Fourier-smear identity evaluates the result.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LevyKhintchineUniqueness.lean lines 241-292, exact source-private lemma intInt_exponent_jump. Parent original smeared_exponent_eq_charFun 3bfe7028.

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat26b_intInt_exponent_jump {ν : Measure ℝ}
    (hν : IsLevyMeasure ν) (ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, (∫ x, levyCompensatedIntegrand (ξ + u) x ∂ν)
      = 2 * ((∫ x, levyCompensatedIntegrand ξ x ∂ν)
          - ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) ∂ν) := by sorry
