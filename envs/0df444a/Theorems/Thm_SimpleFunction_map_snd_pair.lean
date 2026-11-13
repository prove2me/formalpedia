-- Prove2me | Theorems.Thm_SimpleFunction_map_snd_pair
-- name    : SimpleFunction.map_snd_pair
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:27:56.621084+00:00
-- url     : https://prove2.me/theorems/6990ab43-d0a6-4865-9a3b-2aa7e336e624
-- title:
--   ProbabilityTheory_chapter_06_def_6_1_F001: SimpleFunction.map_snd_pair
-- statement:
--   Source theorem `SimpleFunction.map_snd_pair` from `ProbabilityTheory.chapter_06.def_6_1`. The formal Lean declaration specifies its proposition.
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

theorem map_snd_pair (X Y : SimpleFunction Ω) :
    (X.pair Y).map Prod.snd = Y := by
  sorry
end SimpleFunction
