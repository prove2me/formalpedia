-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_polynomialCoefficientProjection_map
-- name    : PermanentFormulaLowerBound.polynomialCoefficientProjection_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/de520a1d-3769-437f-a8f0-9cd698e3063d
-- title:
--   PermanentFormulaLowerBound.polynomialCoefficientProjection_map
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
noncomputable section
variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

theorem PermanentFormulaLowerBound.polynomialCoefficientProjection_map
    (φ : E →ₗ[K] K)
    (hφ : ∀ a : K, φ (algebraMap K E a) = a)
    (p : MvPolynomial ι K) :
    polynomialCoefficientProjection φ
        (MvPolynomial.map (algebraMap K E) p) = p := by sorry
