-- Prove2me | Theorems.Thm_Refinement_sum_block_increment
-- name    : Refinement.sum_block_increment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:51:43.597666+00:00
-- url     : https://prove2.me/theorems/899ba9d7-ef38-4979-a25c-32386a9ca9e8
-- title:
--   Chapter 1, thm_1_2: Refinement.sum_block_increment
-- statement:
--   Source theorem `Refinement.sum_block_increment` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F010
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

theorem Refinement.sum_block_increment
    {a b : ℝ} {α : ℝ → ℝ}
    {P P' : Partition a b}
    (R : Refinement P P')
    (i : Fin P.n) :
    Finset.sum (R.block i)
      (fun j => α (P'.pts j.succ) - α (P'.pts j.castSucc))
      =
    α (P.pts i.succ) - α (P.pts i.castSucc) := by sorry

namespace Partition

end Partition

end Darboux_fundamental_result
