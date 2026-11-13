-- Prove2me | Theorems.Thm_SimpleFunction_map_fst_pair
-- name    : SimpleFunction.map_fst_pair
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:27:45.564525+00:00
-- url     : https://prove2.me/theorems/9720b9ae-73b9-4ac5-9019-5b3a2f184969
-- title:
--   ProbabilityTheory_chapter_06_def_6_1_F001: SimpleFunction.map_fst_pair
-- statement:
--   Source theorem `SimpleFunction.map_fst_pair` from `ProbabilityTheory.chapter_06.def_6_1`. The formal Lean declaration specifies its proposition.
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

theorem map_fst_pair (X Y : SimpleFunction Ω) :
    (X.pair Y).map Prod.fst = X := by
  sorry
end SimpleFunction
