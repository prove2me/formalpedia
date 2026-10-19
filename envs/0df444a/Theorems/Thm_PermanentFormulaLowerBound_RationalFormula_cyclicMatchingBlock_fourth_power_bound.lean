-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_cyclicMatchingBlock_fourth_power_bound
-- name    : PermanentFormulaLowerBound.RationalFormula.cyclicMatchingBlock_fourth_power_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/23d5b08e-cd9f-4af3-913b-bb470c2b6c4c
-- title:
--   PermanentFormulaLowerBound.RationalFormula.cyclicMatchingBlock_fourth_power_bound
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

theorem PermanentFormulaLowerBound.RationalFormula.cyclicMatchingBlock_fourth_power_bound
    {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (m : ℕ) (hhalf : n ≤ 2 * m)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hblock : ∀ x : Fin n × Fin (n / k),
      m * m ≤ 6 * blockLeaves (cyclicMatchingBlock hk x.1 x.2) f) :
    n ^ 4 ≤ 48 * k * variableLeaves f := by sorry
