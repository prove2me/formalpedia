-- Prove2me | Theorems.Thm_SimpleFunction_add_eq_map_pair
-- name    : SimpleFunction.add_eq_map_pair
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:28:12.235279+00:00
-- url     : https://prove2.me/theorems/c34124ad-10f1-40ca-854b-636289e98568
-- title:
--   ProbabilityTheory_chapter_06_def_6_1_F001: SimpleFunction.add_eq_map_pair
-- statement:
--   Source theorem `SimpleFunction.add_eq_map_pair` from `ProbabilityTheory.chapter_06.def_6_1`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_1.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_1_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory
open scoped BigOperators
namespace SimpleFunction
variable {Ω : Type*} [MeasurableSpace Ω]

theorem add_eq_map_pair (X Y : SimpleFunction Ω) :
    X + Y = (X.pair Y).map (fun p => p.1 + p.2) := by
  sorry
end SimpleFunction
