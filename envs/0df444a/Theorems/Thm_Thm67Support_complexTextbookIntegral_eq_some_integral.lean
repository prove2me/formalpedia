-- Prove2me | Theorems.Thm_Thm67Support_complexTextbookIntegral_eq_some_integral
-- name    : Thm67Support.complexTextbookIntegral_eq_some_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:31:12.647192+00:00
-- url     : https://prove2.me/theorems/089cb0b4-8ce5-4b69-9edb-a8f5cdff61b1
-- title:
--   ProbabilityTheory_chapter_06_thm_6_7_F000: Thm67Support.complexTextbookIntegral_eq_some_integral
-- statement:
--   Source theorem `Thm67Support.complexTextbookIntegral_eq_some_integral` from `ProbabilityTheory.chapter_06.thm_6_7`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_7.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory
namespace Thm67Support

theorem complexTextbookIntegral_eq_some_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z) (hZ : Integrable Z μ) :
    complexTextbookIntegral μ Z = some (∫ ω, Z ω ∂μ) := by
  sorry
end Thm67Support
