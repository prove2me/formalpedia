-- Prove2me | Theorems.Thm_Vitali_set_instInfiniteQ_I_Type
-- name    : Vitali_set.instInfiniteQ_I_Type
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T16:30:27.855667+00:00
-- url     : https://prove2.me/theorems/548541cc-4d1e-4d11-9959-0837544cb054
-- title:
--   Chapter 2, thm_2_9: Vitali_set.instInfiniteQ_I_Type
-- statement:
--   Source theorem `Vitali_set.instInfiniteQ_I_Type` from Chapter 2, module `thm_2_9`. Its exact formal statement is shown below and awaits a mathematical read-back.
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

@[instance]

theorem instInfiniteQ_I_Type : Infinite Q_I_Type := by sorry

end Vitali_set
