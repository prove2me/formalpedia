-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat26_norm_compensated_minimal
-- name    : ProbabilityTheory.leanlevy_chat26_norm_compensated_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:22:12.099966+00:00
-- url     : https://prove2.me/theorems/5cec293a-9b9c-4f9b-b664-48794b2614f0
-- title:
--   Public minimal-import compensated Levy Fourier norm bound
-- statement:
--   The compensated Levy Fourier integrand is dominated by the quadratic Levy-measure integrability weight, with a polynomial frequency constant, using the original two-case exponential Taylor estimate.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/CompensatedIntegral.lean lines 97-156, source-exact import-minimal promotion of already Proved original norm theorem 4e6d6642.

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory ProbabilityTheory Complex ENNReal Set
open scoped NNReal ENNReal ComplexConjugate

theorem ProbabilityTheory.leanlevy_chat26_norm_compensated_minimal (ξ x : ℝ) :
    ‖levyCompensatedIntegrand ξ x‖ ≤ (2 + 3 * ξ ^ 2) * min 1 (x ^ 2) := by sorry
