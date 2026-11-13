-- Prove2me | Theorems.Thm_Thm66Support_complexTextbookIntegrable_iff_complexAbsIntegral_lt_top
-- name    : Thm66Support.complexTextbookIntegrable_iff_complexAbsIntegral_lt_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:15:54.907824+00:00
-- url     : https://prove2.me/theorems/264c4032-4cd7-4d46-899a-f9ca12d6bc8d
-- title:
--   ProbabilityTheory_chapter_06_thm_6_6_F000: Thm66Support.complexTextbookIntegrable_iff_complexAbsIntegral_lt_top
-- statement:
--   Source theorem `Thm66Support.complexTextbookIntegrable_iff_complexAbsIntegral_lt_top` extracted from `ProbabilityTheory.chapter_06.thm_6_6`. The formal Lean declaration specifies the proposition.
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

theorem complexTextbookIntegrable_iff_complexAbsIntegral_lt_top {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ) (hZm : Measurable Z) :
    complexTextbookIntegrable μ Z ↔ complexAbsIntegral μ Z < ⊤ := by
  sorry
end Thm66Support
