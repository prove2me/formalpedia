-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_Formula_matching_block_four_leaves_of_coefficientTranscendenceDegree
-- name    : PermanentFormulaLowerBound.Formula.matching_block_four_leaves_of_coefficientTranscendenceDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/a2951749-26dd-42e9-a0c9-62af5eda1a1e
-- title:
--   PermanentFormulaLowerBound.Formula.matching_block_four_leaves_of_coefficientTranscendenceDegree
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
open PermanentFormulaLowerBound.Formula

theorem PermanentFormulaLowerBound.Formula.matching_block_four_leaves_of_coefficientTranscendenceDegree
    {n m : ℕ} {Y : Type*} [Fintype Y] [Nonempty Y]
    (d : Y ↪ Fin n × Fin n)
    (f : Formula (Fin n × Fin n) ℂ)
    (hf : eval f = permanentPolynomial n)
    (htd : ((m * m : ℕ) : Cardinal) ≤
      coefficientTranscendenceDegree (matchingMarkedPermanent d)) :
    m * m ≤ 4 * blockLeaves (matchingMarkedFinset d) f := by sorry
