-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_matching_block_six_leaves_of_coefficientTranscendenceDegree
-- name    : PermanentFormulaLowerBound.RationalFormula.matching_block_six_leaves_of_coefficientTranscendenceDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/cae56fbc-aa78-41a2-9144-0d67e08a57be
-- title:
--   PermanentFormulaLowerBound.RationalFormula.matching_block_six_leaves_of_coefficientTranscendenceDegree
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

theorem PermanentFormulaLowerBound.RationalFormula.matching_block_six_leaves_of_coefficientTranscendenceDegree
    {n m : ℕ} {Y : Type*} [Fintype Y] [Nonempty Y]
    (d : Y ↪ Fin n × Fin n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hvalid : Valid f)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n))
    (htd : ((m * m : ℕ) : Cardinal) ≤
      coefficientTranscendenceDegree (matchingMarkedPermanent d)) :
    m * m ≤ 6 * blockLeaves (matchingMarkedFinset d) f := by sorry
