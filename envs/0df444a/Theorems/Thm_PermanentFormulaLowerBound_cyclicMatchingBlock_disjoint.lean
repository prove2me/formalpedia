-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_cyclicMatchingBlock_disjoint
-- name    : PermanentFormulaLowerBound.cyclicMatchingBlock_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/42eb0e4b-2e22-4c44-afc7-d8e511aa748e
-- title:
--   PermanentFormulaLowerBound.cyclicMatchingBlock_disjoint
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

theorem PermanentFormulaLowerBound.cyclicMatchingBlock_disjoint {n k : ℕ}
    (hk : 0 < k) (x y : Fin n × Fin (n / k)) (hxy : x ≠ y) :
    Disjoint (cyclicMatchingBlock hk x.1 x.2)
      (cyclicMatchingBlock hk y.1 y.2) := by sorry
