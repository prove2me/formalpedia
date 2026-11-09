-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat24_re_one_sub_charFun_eq_integral
-- name    : ProbabilityTheory.leanlevy_chat24_re_one_sub_charFun_eq_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:25:17.687013+00:00
-- url     : https://prove2.me/theorems/3ccfb300-83c2-4734-bddf-459268ef141e
-- title:
--   Real part of one minus the characteristic function is a cosine integral
-- statement:
--   For a probability measure on the reals, the real part of one minus its characteristic function is the expectation of one minus the cosine. This identity controls scaled jump second moments.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean lines 1623-1654; original private lemmas integrable_charFun_integrand and re_one_sub_charFun_eq_integral

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.leanlevy_chat24_re_one_sub_charFun_eq_integral {μ : Measure ℝ} [IsProbabilityMeasure μ] (ξ : ℝ) : (1 - charFun μ ξ).re = ∫ x, (1 - Real.cos (ξ * x)) ∂μ := by sorry
