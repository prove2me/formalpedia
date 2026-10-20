-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_bit_coefficients_algebraicIndependent
-- name    : PermanentFormulaLowerBound.matchingMarkedPermanent_bit_coefficients_algebraicIndependent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/5f170d08-ef39-4e43-8e6c-d36979f13888
-- title:
--   PermanentFormulaLowerBound.matchingMarkedPermanent_bit_coefficients_algebraicIndependent
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

theorem PermanentFormulaLowerBound.matchingMarkedPermanent_bit_coefficients_algebraicIndependent
    {ell m : ℕ} (p q : Fin m → ℂ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    AlgebraicIndependent ℂ
      (fun de : Fin m × Fin m =>
        coefficientPolynomial
          (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
          (matchingSquarefreeMonomial
            (matchingBitCoefficientSet ell m de))) := by sorry
