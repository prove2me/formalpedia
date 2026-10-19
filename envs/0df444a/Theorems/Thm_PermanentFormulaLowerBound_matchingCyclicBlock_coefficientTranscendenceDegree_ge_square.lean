-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingCyclicBlock_coefficientTranscendenceDegree_ge_square
-- name    : PermanentFormulaLowerBound.matchingCyclicBlock_coefficientTranscendenceDegree_ge_square
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/b4793db9-82dc-4ebd-9d7f-2f77e97d7010
-- title:
--   PermanentFormulaLowerBound.matchingCyclicBlock_coefficientTranscendenceDegree_ge_square
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

theorem PermanentFormulaLowerBound.matchingCyclicBlock_coefficientTranscendenceDegree_ge_square
    {n ell m : ℕ}
    (hk : 0 < 2 * ell) (hn : n = (ell + ell) + m)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree
      (matchingMarkedPermanent (matchingCyclicDiagonalEmbedding hk t j)) := by sorry
