-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_Formula_cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
-- name    : PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/a6216fd5-385c-4088-b5ae-3273d39b1e00
-- title:
--   PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
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

theorem PermanentFormulaLowerBound.Formula.cyclicMatchingBlock_fourth_power_bound_of_coefficientTranscendenceDegree
    {n ell m : ℕ}
    (hk : 0 < 2 * ell) (hkn : 2 * ell ≤ n) (hhalf : n ≤ 2 * m)
    (f : Formula (Fin n × Fin n) ℂ)
    (hf : eval f = permanentPolynomial n)
    (hcertificate : ∀ x : Fin n × Fin (n / (2 * ell)),
      ((m * m : ℕ) : Cardinal) ≤ coefficientTranscendenceDegree
        (matchingMarkedPermanent
          (matchingCyclicDiagonalEmbedding hk x.1 x.2))) :
    n ^ 4 ≤ 32 * (2 * ell) * variableLeaves f := by sorry
