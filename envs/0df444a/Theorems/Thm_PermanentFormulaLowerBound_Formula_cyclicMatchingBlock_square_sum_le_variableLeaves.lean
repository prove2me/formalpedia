-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_Formula_cyclicMatchingBlock_square_sum_le_variableLeaves
-- name    : PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_square_sum_le_variableLeaves
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/f06be5e8-d228-4629-926a-265b0a7ec615
-- title:
--   PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_square_sum_le_variableLeaves
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

theorem PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_square_sum_le_variableLeaves
    {n k : ℕ} (hk : 0 < k) (m : ℕ)
    (f : Formula (Fin n × Fin n) ℂ)
    (hblock : ∀ x : Fin n × Fin (n / k),
      m * m ≤ 4 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f) :
    (n * (n / k)) * (m * m) ≤ 4 * variableLeaves f := by sorry
