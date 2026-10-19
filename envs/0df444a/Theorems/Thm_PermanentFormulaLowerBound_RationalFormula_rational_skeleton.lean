-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_rational_skeleton
-- name    : PermanentFormulaLowerBound.RationalFormula.rational_skeleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/b9955e50-94f0-4d24-bf4c-1b1d271b1307
-- title:
--   PermanentFormulaLowerBound.RationalFormula.rational_skeleton
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
noncomputable section
variable {Y Z F : Type*}

theorem PermanentFormulaLowerBound.RationalFormula.rational_skeleton [Field F]
    (f : RationalFormula (Y ⊕ Z) F) (hvalid : Valid f)
    (hmarked : 0 < yLeafCount f) :
    ∃ s : Finset (rationalCoefficientField Z F),
      s.card ≤ 6 * yLeafCount f - 3 ∧
        splitEval f ∈ rationalSkeletonField (Y := Y) s := by sorry
