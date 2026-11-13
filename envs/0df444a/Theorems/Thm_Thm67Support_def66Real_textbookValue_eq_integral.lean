-- Prove2me | Theorems.Thm_Thm67Support_def66Real_textbookValue_eq_integral
-- name    : Thm67Support.def66Real_textbookValue_eq_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:30:58.926774+00:00
-- url     : https://prove2.me/theorems/4658364b-3f6c-46bc-b1df-761bec069300
-- title:
--   ProbabilityTheory_chapter_06_thm_6_7_F000: Thm67Support.def66Real_textbookValue_eq_integral
-- statement:
--   Source theorem `Thm67Support.def66Real_textbookValue_eq_integral` from `ProbabilityTheory.chapter_06.thm_6_7`. The formal Lean declaration specifies its proposition.
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

theorem def66Real_textbookValue_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    Def66RealSupport.textbookValue μ (fun ω => (f ω : EReal)) = ∫ ω, f ω ∂μ := by
  sorry
end Thm67Support
