-- Prove2me | Theorems.Thm_Thm67Support_def66Real_textbookIntegrable_iff
-- name    : Thm67Support.def66Real_textbookIntegrable_iff
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:30:31.086201+00:00
-- url     : https://prove2.me/theorems/c1e9754b-b17b-412e-9e85-10422d1dd6bb
-- title:
--   ProbabilityTheory_chapter_06_thm_6_7_F000: Thm67Support.def66Real_textbookIntegrable_iff
-- statement:
--   Source theorem `Thm67Support.def66Real_textbookIntegrable_iff` from `ProbabilityTheory.chapter_06.thm_6_7`. The formal Lean declaration specifies its proposition.
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

theorem def66Real_textbookIntegrable_iff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) :
    Def66RealSupport.textbookIntegrable μ (fun ω => (f ω : EReal)) ↔ Integrable f μ := by
  sorry
end Thm67Support
