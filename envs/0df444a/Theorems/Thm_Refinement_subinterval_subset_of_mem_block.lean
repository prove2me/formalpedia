-- Prove2me | Theorems.Thm_Refinement_subinterval_subset_of_mem_block
-- name    : Refinement.subinterval_subset_of_mem_block
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:51:18.555246+00:00
-- url     : https://prove2.me/theorems/805ae608-bcc9-4728-b276-8d7874edf2ff
-- title:
--   Chapter 1, thm_1_2: Refinement.subinterval_subset_of_mem_block
-- statement:
--   Source theorem `Refinement.subinterval_subset_of_mem_block` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
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

theorem Refinement.subinterval_subset_of_mem_block
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n}
    (hj : j ∈ R.block i) :
    Partition.subinterval P' j ⊆ Partition.subinterval P i := by sorry

namespace Partition

end Partition

end Darboux_fundamental_result
