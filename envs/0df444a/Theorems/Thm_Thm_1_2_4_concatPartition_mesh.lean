-- Prove2me | Theorems.Thm_Thm_1_2_4_concatPartition_mesh
-- name    : Thm_1_2_4.concatPartition_mesh
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:54:14.839212+00:00
-- url     : https://prove2.me/theorems/99782f4c-8249-4b1b-b587-067c49d2ab49
-- title:
--   Chapter 1, thm_1_2_4: Thm_1_2_4.concatPartition_mesh
-- statement:
--   Source theorem `Thm_1_2_4.concatPartition_mesh` from Chapter 1, module `thm_1_2_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F000
import Mathlib.Tactic

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

noncomputable section SubintervalIntegrability

theorem concatPartition_mesh {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) :
    (concatPartition P1 P2).mesh ≤ max P1.mesh P2.mesh := by sorry

end SubintervalIntegrability

end Thm_1_2_4  

end Thm_1_2_4
