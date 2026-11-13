-- Prove2me | Theorems.Thm_Vitali_set_vitali_covers_Ico
-- name    : Vitali_set.vitali_covers_Ico
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:39:43.055214+00:00
-- url     : https://prove2.me/theorems/8bb9bae6-f90d-4ef0-9a5e-b84ff962f332
-- title:
--   Chapter 2, thm_2_9: Vitali_set.vitali_covers_Ico
-- statement:
--   Source theorem `Vitali_set.vitali_covers_Ico` from Chapter 2, module `thm_2_9`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_9.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F001
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.Tactic

noncomputable section Vitali_set

namespace Vitali_set

open Classical   
open Rat
open Set

theorem vitali_covers_Ico : Ico 0 1 ⊆ ⋃ n, VitaliSeq n := by sorry

end Vitali_set
