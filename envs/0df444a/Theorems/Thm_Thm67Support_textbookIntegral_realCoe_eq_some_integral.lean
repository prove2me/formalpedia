-- Prove2me | Theorems.Thm_Thm67Support_textbookIntegral_realCoe_eq_some_integral
-- name    : Thm67Support.textbookIntegral_realCoe_eq_some_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:30:45.446202+00:00
-- url     : https://prove2.me/theorems/26b9c7f6-491e-4e25-90c6-c56dfba8576c
-- title:
--   ProbabilityTheory_chapter_06_thm_6_7_F000: Thm67Support.textbookIntegral_realCoe_eq_some_integral
-- statement:
--   Source theorem `Thm67Support.textbookIntegral_realCoe_eq_some_integral` from `ProbabilityTheory.chapter_06.thm_6_7`. The formal Lean declaration specifies its proposition.
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

theorem textbookIntegral_realCoe_eq_some_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    textbookIntegral μ (fun ω => (f ω : EReal)) = some ((∫ ω, f ω ∂μ : ℝ) : EReal) := by
  sorry
end Thm67Support
