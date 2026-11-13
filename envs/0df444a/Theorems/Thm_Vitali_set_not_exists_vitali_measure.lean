-- Prove2me | Theorems.Thm_Vitali_set_not_exists_vitali_measure
-- name    : Vitali_set.not_exists_vitali_measure
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:40:30.175121+00:00
-- url     : https://prove2.me/theorems/89ef48d7-60d3-4d87-a557-530c2a974a02
-- title:
--   Chapter 2, thm_2_9: Vitali_set.not_exists_vitali_measure
-- statement:
--   Source theorem `Vitali_set.not_exists_vitali_measure` from Chapter 2, module `thm_2_9`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_9.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F000
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.Tactic

noncomputable section Vitali_set

namespace Vitali_set

open Classical   
open Rat
open Set

theorem not_exists_vitali_measure : ¬ ∃ m, IsVitaliMeasure m := by sorry

end Vitali_set
