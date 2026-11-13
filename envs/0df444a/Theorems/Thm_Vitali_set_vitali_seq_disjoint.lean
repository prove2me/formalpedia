-- Prove2me | Theorems.Thm_Vitali_set_vitali_seq_disjoint
-- name    : Vitali_set.vitali_seq_disjoint
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:38:55.491197+00:00
-- url     : https://prove2.me/theorems/7290b3d6-cde8-4a4d-b12b-c6372c37797f
-- title:
--   Chapter 2, thm_2_9: Vitali_set.vitali_seq_disjoint
-- statement:
--   Source theorem `Vitali_set.vitali_seq_disjoint` from Chapter 2, module `thm_2_9`. Its exact formal statement is shown below and awaits a mathematical read-back.
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

theorem vitali_seq_disjoint : Pairwise (fun i j => Disjoint (VitaliSeq i) (VitaliSeq j)) := by sorry

end Vitali_set
