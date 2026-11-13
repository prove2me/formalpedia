-- Prove2me | Theorems.Thm_Thm66Support_textbookIntegrable_iff_realAbsIntegral_lt_top
-- name    : Thm66Support.textbookIntegrable_iff_realAbsIntegral_lt_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:15:32.390556+00:00
-- url     : https://prove2.me/theorems/4b93ad72-e672-4c69-b7d4-7af8d06a4697
-- title:
--   ProbabilityTheory_chapter_06_thm_6_6_F000: Thm66Support.textbookIntegrable_iff_realAbsIntegral_lt_top
-- statement:
--   Source theorem `Thm66Support.textbookIntegrable_iff_realAbsIntegral_lt_top` extracted from `ProbabilityTheory.chapter_06.thm_6_6`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_6.lean

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_6_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory
namespace Thm66Support
open Def66RealSupport

theorem textbookIntegrable_iff_realAbsIntegral_lt_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EReal) :
    textbookIntegrable μ X ↔ realAbsIntegral μ X < ⊤ := by
  sorry
end Thm66Support
