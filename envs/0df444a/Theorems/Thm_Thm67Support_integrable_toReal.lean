-- Prove2me | Theorems.Thm_Thm67Support_integrable_toReal
-- name    : Thm67Support.integrable_toReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:31:54.564959+00:00
-- url     : https://prove2.me/theorems/6a3ae5f4-72b5-4522-8874-ecc0161b08cf
-- title:
--   ProbabilityTheory_chapter_06_thm_6_7_F000: Thm67Support.integrable_toReal
-- statement:
--   Source theorem `Thm67Support.integrable_toReal` from `ProbabilityTheory.chapter_06.thm_6_7`. The formal Lean declaration specifies its proposition.
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

theorem integrable_toReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    Integrable (fun ω => (X ω).toReal) μ := by
  sorry
end Thm67Support
