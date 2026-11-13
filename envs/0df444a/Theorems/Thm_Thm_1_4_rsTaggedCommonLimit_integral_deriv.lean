-- Prove2me | Theorems.Thm_Thm_1_4_rsTaggedCommonLimit_integral_deriv
-- name    : Thm_1_4.rsTaggedCommonLimit_integral_deriv
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:12:49.173246+00:00
-- url     : https://prove2.me/theorems/cf77fd3c-a1b4-4e27-b3df-f6213272b7cf
-- title:
--   ProbabilityTheory_chapter_01_thm_1_4_F005: Thm_1_4.rsTaggedCommonLimit_integral_deriv
-- statement:
--   Source theorem `Thm_1_4.rsTaggedCommonLimit_integral_deriv` from `ProbabilityTheory.chapter_01.thm_1_4`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F002

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
open Set MeasureTheory
open scoped BigOperators Pointwise Interval
noncomputable section
namespace Thm_1_4

theorem rsTaggedCommonLimit_integral_deriv
    {f α α' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : MonotoneOn α (Set.Icc a b))
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Set.Icc a b)) :
    rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x) := by
  sorry
end Thm_1_4
end
