-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat26_smear_integrand_public
-- name    : ProbabilityTheory.leanlevy_chat26_smear_integrand_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:19:35.069542+00:00
-- url     : https://prove2.me/theorems/7ad877ad-009b-4f49-81e4-7cd722192b09
-- title:
--   Public compensated Levy integrand frequency-smearing identity
-- statement:
--   Averaging the compensated Levy integrand over a symmetric frequency interval cancels the linear compensator, leaving the Fourier exponential weighted by one minus sinc.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LevyKhintchineUniqueness.lean source-private pointwise smear lemma; accepted original private target 98e04d36; substitute the extensionally identical Proved/public shifted-exp helper ce401989.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_ProbabilityTheory_leanlevy_chat23_intInt_exp_shift
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat26_smear_integrand_public (ξ x : ℝ) :
    levyCompensatedIntegrand ξ x
        - (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, levyCompensatedIntegrand (ξ + u) x
      = Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) := by sorry
