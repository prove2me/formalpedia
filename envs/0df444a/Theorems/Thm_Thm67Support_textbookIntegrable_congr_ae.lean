-- Prove2me | Theorems.Thm_Thm67Support_textbookIntegrable_congr_ae
-- name    : Thm67Support.textbookIntegrable_congr_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:32:08.462202+00:00
-- url     : https://prove2.me/theorems/3ba258fa-3eb1-4c48-a9e4-9acd90721c72
-- title:
--   ProbabilityTheory_chapter_06_thm_6_7_F000: Thm67Support.textbookIntegrable_congr_ae
-- statement:
--   Source theorem `Thm67Support.textbookIntegrable_congr_ae` from `ProbabilityTheory.chapter_06.thm_6_7`. The formal Lean declaration specifies its proposition.
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

theorem textbookIntegrable_congr_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → EReal} (h : X =ᵐ[μ] Y) :
    textbookIntegrable μ X ↔ textbookIntegrable μ Y := by
  sorry
end Thm67Support
