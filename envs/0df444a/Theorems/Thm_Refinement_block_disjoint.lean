-- Prove2me | Theorems.Thm_Refinement_block_disjoint
-- name    : Refinement.block_disjoint
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:52:11.643558+00:00
-- url     : https://prove2.me/theorems/f1bcfd77-2569-4911-9474-fa115cefc890
-- title:
--   Chapter 1, thm_1_2: Refinement.block_disjoint
-- statement:
--   Source theorem `Refinement.block_disjoint` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
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

theorem Refinement.block_disjoint
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i k : Fin P.n} (hik : i ≠ k) :
    Disjoint (R.block i) (R.block k) := by sorry

namespace Partition

end Partition

end Darboux_fundamental_result
