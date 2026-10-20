-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPermanentJacobian_eq_weighted
-- name    : PermanentFormulaLowerBound.matchingPermanentJacobian_eq_weighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/ea37b196-7393-47d3-9b78-4df8071c0083
-- title:
--   PermanentFormulaLowerBound.matchingPermanentJacobian_eq_weighted
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

theorem PermanentFormulaLowerBound.matchingPermanentJacobian_eq_weighted
    {ell m : ℕ} (p q : Fin m → ℂ) :
    matchingPermanentJacobian (ell := ell) p q =
      matchingWeightedBivariateEvaluationMatrix p q
        (fun d : Fin m => matchingBitSubset ell (d : ℕ))
        (fun e : Fin m => matchingBitSubset ell (e : ℕ)) := by sorry
