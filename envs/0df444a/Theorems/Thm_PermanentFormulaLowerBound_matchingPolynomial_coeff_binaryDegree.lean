-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_coeff_binaryDegree
-- name    : PermanentFormulaLowerBound.matchingPolynomial_coeff_binaryDegree
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/062130c3-a992-4f08-a1a7-3d4ff8315633
-- title:
--   PermanentFormulaLowerBound.matchingPolynomial_coeff_binaryDegree
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

theorem PermanentFormulaLowerBound.matchingPolynomial_coeff_binaryDegree {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) :
    (matchingPolynomial p P).coeff (matchingBinaryDegree P) =
      (-1 : F) ^ P.card * (P.card.factorial : F) := by sorry
